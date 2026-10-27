\ net/tcp.fs: TCP, for servers. LISTEN on a port; connections that complete the
\ handshake queue for ACCEPT-CONNECTION. The application uses SEND, SEND-LINE,
\ GET-LINE and CLOSE-CONNECTION, sleeping while it waits; the network task wakes
\ it when something changes. Lost segments are resent, go-back-N, with an
\ exponentially growing timeout. Out-of-order segments are dropped: the sender
\ resends them.
\
\ Each connection counts bytes: acknowledged, sent and queued on the way out;
\ received and consumed on the way in. Sequence numbers follow from the counts.
\
\ Against attackers off the path: initial sequence numbers are a keyed hash
\ (RFC 6528); resets, SYNs and acknowledgements must be where we expect them,
\ or they get a challenge ACK or are dropped (RFC 5961); connections and
\ half-open ones are capped, and a SYN beyond the caps is dropped.

-269 message: connection closed
-270 message: no free listening port slot

\ ---- Segments

0 constant tcp-sport
2 constant tcp-dport
4 constant tcp-seq
8 constant tcp-ack
12 constant tcp-flags          \ data offset (in words) in the top 4 bits
14 constant tcp-window
16 constant tcp-checksum
20 constant /tcp
1 constant f-fin
2 constant f-syn
4 constant f-rst
8 constant f-psh
16 constant f-ack
1460 constant our-mss          \ the most data per segment we accept

\ ---- Connections

0 constant closed              \ states
1 constant syn-received
2 constant established
3 constant close-wait
4 constant last-ack
5 constant fin-wait-1
6 constant fin-wait-2
7 constant closing
8 constant time-wait

4096 constant /rx              \ ring sizes: powers of two
8192 constant /tx

1 constant fin-queued          \ flags
2 constant fin-sent
4 constant fin-acked
8 constant fin-received
16 constant app-closed
32 constant ack-now

0
1 cells field c.link              \ next in the list of live connections, or of free ones
1 cells field c.state
1 cells field c.lport
1 cells field c.rip
1 cells field c.rport
1 cells field c.iss               \ our initial sequence number
1 cells field c.irs               \ theirs
1 cells field c.tx-acked          \ bytes they have acknowledged
1 cells field c.tx-sent           \ bytes sent, acknowledged or not
1 cells field c.tx-queued         \ bytes the application has given us
1 cells field c.rx-in             \ bytes received in order
1 cells field c.rx-out            \ bytes the application has taken
1 cells field c.snd-wnd           \ how much more they will take
1 cells field c.mss               \ the most data per segment they accept
1 cells field c.rto               \ retransmission timeout, ms
1 cells field c.rexmit            \ when to retransmit (a deadline), or 0
1 cells field c.retries
1 cells field c.flags
1 cells field c.timeout           \ when TIME-WAIT or FIN-WAIT-2 ends
1 cells field c.hlink             \ next in its hash bucket
1 cells field c.owner             \ the task to wake when something changes
1 cells field c.next              \ next in its listener's queue
dup constant /conn-header
/rx field c.rx
/tx field c.tx
constant /conn

variable conns                 \ live connections
variable free-conns            \ recycled ones
1000 constant base-rto
60000 constant max-rto
8 constant max-retries
variable max-syn-retries  4 max-syn-retries !   \ SYN-ACKs sent before a half-open connection goes (about 30 s)
2000 constant time-wait-ms
60000 constant fin-wait-ms     \ how long we wait for their FIN after ours is acknowledged
variable max-conns  256 max-conns !          \ live connections, in any state
variable max-half-open  64 max-half-open !   \ connections still in the handshake

: flag?   ( conn bit -- flag )  swap c.flags @ and 0<> ;
: flag+   ( conn bit -- )  over c.flags @ or swap c.flags ! ;
: wake-owner  ( conn -- )  c.owner @ ?dup if wake then ;

\ ---- Finding connections: a hash table of their addresses and ports, keyed so
\ that outsiders cannot choose ports that all land in one bucket.

: key@  ( addr -- k0 k1 )  dup @ swap cell+ @ ;
create isn-key  random , random ,
create bucket-key  random , random ,
create tuple 2 cells allot
: tuple-hash  ( rip rport lport key -- h )  \ the keyed hash of a connection's addresses and ports
  >r  swap 16 lshift or  swap 32 lshift or  tuple !  my-ip @ tuple cell+ !
  tuple 16 r> key@ siphash ;

256 constant #buckets
create buckets  #buckets cells allot   buckets #buckets cells 0 fill
: bucket  ( rip rport lport -- addr )  bucket-key tuple-hash #buckets 1- and cells buckets + ;
: conn-bucket  ( conn -- addr )  dup c.rip @ over c.rport @ rot c.lport @ bucket ;
: hash-in   ( conn -- )  dup conn-bucket  dup @ 2 pick c.hlink !  ! ;
: hash-out  ( conn -- )
  dup conn-bucket
  begin dup @ while
    dup @ 2 pick = if  swap c.hlink @ swap !  exit  then
    @ c.hlink
  repeat 2drop ;

: new-conn  ( -- conn )  \ from the free list, or new
  free-conns @ ?dup if  dup c.link @ free-conns !  else  /conn reserve  then
  dup /conn-header 0 fill
  base-rto over c.rto !
  conns @ over c.link !  dup conns ! ;
: unlink  ( conn list -- )  \ remove conn from a list linked through c.link
  begin dup @ while
    dup @ 2 pick = if  swap c.link @ swap !  exit  then
    @
  repeat 2drop ;
: free-conn  ( conn -- )
  dup hash-out  dup conns unlink  free-conns @ over c.link !  free-conns ! ;

\ ---- Sequence numbers: 32 bits, wrapping

: s32      ( u -- n )  $ffffffff and  dup $80000000 and if $100000000 - then ;
: snd-una  ( conn -- seq )
  dup c.iss @ 1+ over c.tx-acked @ +  swap fin-acked flag? if 1+ then  $ffffffff and ;
: snd-nxt  ( conn -- seq )
  dup c.iss @ 1+ over c.tx-sent @ +  swap fin-sent flag? if 1+ then  $ffffffff and ;
: rcv-nxt  ( conn -- seq )
  dup c.irs @ 1+ over c.rx-in @ +  swap fin-received flag? if 1+ then  $ffffffff and ;

: in-flight  ( conn -- n )  dup c.tx-sent @ swap c.tx-acked @ - ;
: unsent     ( conn -- n )  dup c.tx-queued @ swap c.tx-sent @ - ;
: rx-unread  ( conn -- n )  dup c.rx-in @ swap c.rx-out @ - ;
: rx-room    ( conn -- n )  /rx swap rx-unread - ;
: tx-room    ( conn -- n )  dup c.tx-queued @ swap c.tx-acked @ - /tx swap - ;
: tx@  ( conn k -- c )  /tx 1- and swap c.tx + c@ ;
: rx@  ( conn k -- c )  /rx 1- and swap c.rx + c@ ;

\ ---- Sending segments (under tx-lock)

: tx-tcp  ( -- addr )  tx-frame ip-payload + ;
variable o-conn  variable o-seq  variable o-flags  variable o-pos  variable o-len

\ A segment from conn: sequence number, flags, and o-len bytes of data from
\ position o-pos of its transmit ring. A SYN carries our MSS.
: (segment-out)  ( conn seq flags pos len -- )
  o-len ! o-pos ! o-flags ! o-seq ! o-conn !
  o-flags @ f-syn and if 24 else 20 then           ( hlen )
  o-conn @ c.lport @ tx-tcp tcp-sport + n16!
  o-conn @ c.rport @ tx-tcp tcp-dport + n16!
  o-seq @ tx-tcp tcp-seq + n32!
  o-flags @ f-ack and if o-conn @ rcv-nxt else 0 then  tx-tcp tcp-ack + n32!
  dup 2 rshift 12 lshift o-flags @ or  tx-tcp tcp-flags + n16!
  o-conn @ rx-room 65535 min  tx-tcp tcp-window + n16!
  0 tx-tcp tcp-checksum + n16!  0 tx-tcp 18 + n16!
  dup 24 = if  $02040000 our-mss or  tx-tcp /tcp + n32!  then
  o-len @ 0 ?do  o-conn @ o-pos @ i + tx@  over tx-tcp + i + c!  loop
  o-len @ +                                        ( seglen )
  my-ip @ o-conn @ c.rip @ 2 pick proto-tcp pseudo-sum  tx-tcp 2 pick sum16 fold
  tx-tcp tcp-checksum + n16!
  proto-tcp o-conn @ c.rip @ ip-send drop ;
: segment-out  ( conn seq flags pos len -- )  ['] (segment-out) tx-lock locked ;

: control-out  ( conn seq flags -- )  0 0 segment-out ;     \ no data
: arm-rexmit   ( conn -- )  dup c.rto @ deadline swap c.rexmit ! ;

: send-data  ( conn n -- conn )  \ the next n unsent bytes
  over dup snd-nxt  f-ack f-psh or  2 pick c.tx-sent @  4 pick  segment-out
  over c.tx-sent +!
  dup c.rexmit @ 0= if dup arm-rexmit then ;
: sendable  ( conn -- n )
  dup unsent  over c.snd-wnd @ 2 pick in-flight - 0 max  min  swap c.mss @ min ;

\ Send what the window allows, then our FIN once everything queued is out;
\ then a bare ACK if one is owed and nothing else carried it. If data waits on
\ a closed window, the retransmission timer is armed to probe it.
variable went                  \ something went out (only used under tx-lock)
: (tcp-output)  ( conn -- )
  0 went !
  dup c.state @ dup established = swap close-wait = or if
    begin dup sendable ?dup while send-data true went ! repeat
    dup fin-queued flag?  over fin-sent flag? 0= and  over unsent 0= and if
      dup dup snd-nxt f-fin f-ack or control-out  true went !
      dup fin-sent flag+
      dup c.state @ established = if fin-wait-1 else last-ack then  over c.state !
      dup c.rexmit @ 0= if dup arm-rexmit then
    then
    dup unsent 0>  over c.rexmit @ 0= and if dup arm-rexmit then
  then
  dup ack-now flag?  went @ 0= and if  dup dup snd-nxt f-ack control-out  then
  dup c.flags @ ack-now invert and swap c.flags ! ;
: tcp-output  ( conn -- )  ['] (tcp-output) tx-lock locked ;

\ ---- Listening

8 constant #listeners
create listeners  #listeners 3 cells * allot   listeners #listeners 3 cells * 0 fill
: listen-slot  ( i -- addr )  3 cells * listeners + ; \ port, queue head, waiting task
: listener-of  ( port -- l | 0 )
  #listeners 0 do  dup i listen-slot @ = if  drop i listen-slot unloop exit  then  loop
  drop 0 ;
: listen  ( port -- )  \ accept connections on port
  dup listener-of if drop exit then
  0 listener-of dup 0= if -270 throw then  ! ;

: enqueue  ( conn l -- )  \ a connection ready to accept, at the end of the queue
  0 2 pick c.next !
  dup >r cell+  begin dup @ while @ c.next repeat  !
  r> 2 cells + @ ?dup if wake then ;

: accept-connection  ( port -- conn )  \ wait for the next connection on port
  listener-of dup 0= if -24 throw then
  begin dup cell+ @ 0= while  up@ over 2 cells + !  stop  repeat
  0 over 2 cells + !
  cell+ dup @ tuck c.next @ swap !
  up@ over c.owner ! ;

\ ---- Receiving segments. These hold the fields of the segment being handled,
\ in the network task.

variable i-seq  variable i-ack  variable i-flags  variable i-wnd  variable i-mss
variable i-data  variable i-len  variable i-sport  variable i-dport

: i-flag?  ( bit -- flag )  i-flags @ and 0<> ;

: find-conn  ( -- conn | 0 )  \ the live connection the segment belongs to
  ip-source i-sport @ i-dport @ bucket @
  begin dup while
    dup c.rport @ i-sport @ =  over c.lport @ i-dport @ = and
    over c.rip @ ip-source = and  over c.state @ closed <> and  if exit then
    c.hlink @
  repeat ;

: options-mss  ( segment hlen -- )  \ the MSS option of a SYN; 536 without one
  536 i-mss !
  over + swap /tcp +                                ( end p )
  begin 2dup > while
    dup c@  dup 0= if 2drop drop exit then         \ end of options
    1 = if
      1+                                            \ no-op
    else
      dup c@ 2 =  over 1+ c@ 4 = and if  dup 2 + n16@ i-mss !  then
      dup 1+ c@ 1 max +
    then
  repeat 2drop ;

\ A reset for a segment that belongs to no connection, sent from a scratch record.
create rst-conn  /conn-header allot
: refuse  ( -- )
  f-rst i-flag? if exit then
  rst-conn /conn-header 0 fill
  i-dport @ rst-conn c.lport !  i-sport @ rst-conn c.rport !  ip-source rst-conn c.rip !
  f-ack i-flag? if
    rst-conn i-ack @ f-rst control-out
  else                                              \ acknowledge all of it
    i-seq @ i-len @ +  f-syn i-flag? -  f-fin i-flag? -  1- rst-conn c.irs !
    rst-conn 0 f-rst f-ack or control-out
  then ;

: new-iss  ( -- seq )  \ RFC 6528: a clock, plus a keyed hash of the addresses and ports
  ip-source i-sport @ i-dport @ isn-key tuple-hash  counter 4 rshift +  $ffffffff and ;

: count-list  ( conn -- n )  0 swap begin ?dup while swap 1+ swap c.link @ repeat ;
: half-open  ( -- n )  \ connections still in the handshake
  0 conns @ begin ?dup while
    dup c.state @ syn-received = if swap 1+ swap then  c.link @
  repeat ;
: room?  ( -- flag )  \ a new connection is within the caps
  conns @ count-list max-conns @ <  half-open max-half-open @ < and ;

: open-conn  ( -- )  \ a SYN to a listening port: answer it
  new-conn >r
  syn-received r@ c.state !
  i-dport @ r@ c.lport !  i-sport @ r@ c.rport !  ip-source r@ c.rip !
  i-seq @ r@ c.irs !
  new-iss r@ c.iss !
  i-wnd @ r@ c.snd-wnd !  i-mss @ our-mss min 64 max r@ c.mss !
  r@ hash-in
  r@ dup c.iss @ f-syn f-ack or control-out
  r> arm-rexmit ;

\ It is over: recycle it once the application is done with it. One still in the
\ handshake was never handed to an application, so it is recycled now.
: release-conn  ( conn -- )
  dup c.state @ syn-received = if dup app-closed flag+ then
  closed over c.state !  0 over c.rexmit !
  dup wake-owner
  dup app-closed flag? if free-conn else drop then ;

: time-wait!  ( conn -- )  time-wait over c.state !  time-wait-ms deadline swap c.timeout ! ;

: acked  ( conn -- )  \ the segment's acknowledgement moves snd-una on
  i-ack @ over snd-una - s32                        ( conn n )
  dup 0> 0= if 2drop exit then
  over snd-nxt 2 pick snd-una - s32  over < if 2drop exit then   \ beyond what we sent
  over in-flight min  over c.tx-acked +!
  dup fin-sent flag?  i-ack @ 2 pick snd-nxt = and if  dup fin-acked flag+  then
  base-rto over c.rto !  0 over c.retries !
  dup snd-una over snd-nxt = if  0 over c.rexmit !  else  dup arm-rexmit  then
  wake-owner ;

: fin-acked-in  ( conn -- )  \ what our FIN being acknowledged changes
  dup fin-acked flag? 0= if drop exit then
  dup c.state @
  dup fin-wait-1 = if                               \ they may never send theirs: time out
    drop  fin-wait-2 over c.state !  fin-wait-ms deadline swap c.timeout ! exit
  then
  dup closing = if  drop time-wait! exit  then
  last-ack = if release-conn else drop then ;

: data-in  ( conn -- )  \ in-order data, as much as fits; anything else is dropped
  i-len @ 0= if drop exit then
  dup fin-received flag? if drop exit then
  i-seq @ over rcv-nxt <> if  ack-now flag+ exit  then   \ say where we are
  dup rx-room i-len @ min                           ( conn n )
  dup 0 ?do
    i-data @ i + c@  2 pick c.rx-in @ i + /rx 1- and  3 pick c.rx + c!
  loop
  over c.rx-in +!
  dup ack-now flag+  wake-owner ;

: fin-in  ( conn -- )  \ their FIN, once everything before it has arrived
  f-fin i-flag? 0= if drop exit then
  dup fin-received flag? if  ack-now flag+ exit  then    \ sent again: our ACK was lost
  i-seq @ i-len @ +  over rcv-nxt <> if drop exit then
  dup fin-received flag+  dup ack-now flag+  dup wake-owner
  dup c.state @
  dup established = if  drop close-wait swap c.state ! exit  then
  dup fin-wait-1 = if  drop closing swap c.state ! exit  then
  fin-wait-2 = if time-wait! else drop then ;

: receiving?  ( conn -- flag )  \ in a state that takes data
  c.state @  dup established =  over fin-wait-1 = or  swap fin-wait-2 = or ;

\ RFC 5961. A reset counts only at exactly the next sequence number; elsewhere in
\ the window it gets a challenge ACK, which a real peer answers with an exact
\ reset. An acknowledgement must lie between what we sent and a window before
\ what was acknowledged, or the segment is dropped.
: challenge  ( conn -- )  dup ack-now flag+ tcp-output ;
: rst-in  ( conn -- )
  i-seq @ over rcv-nxt = if  release-conn exit  then
  i-seq @ over rcv-nxt - $ffffffff and  over rx-room u< if challenge else drop then ;
: ack-ok?  ( conn -- flag )
  dup snd-nxt over snd-una - s32  swap i-ack @ swap snd-una - s32   ( sent n )
  tuck < 0=  swap -65535 < 0= and ;

: segment-in  ( conn -- )
  >r
  f-rst i-flag? if  r> rst-in exit  then
  r@ c.state @ syn-received = if
    f-syn i-flag? if  r@ dup c.iss @ f-syn f-ack or control-out  r> drop exit  then
    f-ack i-flag? 0=  i-ack @ r@ c.iss @ 1+ $ffffffff and <>  or if  r> drop exit  then
    established r@ c.state !  0 r@ c.rexmit !  base-rto r@ c.rto !  0 r@ c.retries !
    r@ dup c.lport @ listener-of ?dup if enqueue else drop then
  then
  f-syn i-flag? if  r@ ack-now flag+  r> tcp-output exit  then
  f-ack i-flag? 0= if  r> drop exit  then
  r@ ack-ok? 0= if  r> challenge exit  then
  i-wnd @ r@ c.snd-wnd !
  r@ acked
  r@ fin-acked-in
  r@ c.state @ closed = if  r> drop exit  then      \ released, maybe recycled
  r@ receiving? if r@ data-in then
  r@ fin-in
  r@ c.state @ closed = if  r> drop exit  then
  r> tcp-output ;

: tcp-in  ( segment len -- )
  2dup  ip-source rx-ip ip-dst + n32@ 2 pick proto-tcp pseudo-sum  -rot sum16 fold
  if 2drop exit then
  over tcp-flags + n16@  dup $3f and i-flags !  12 rshift 4 *     ( segment len hlen )
  2dup <  over /tcp < or if 2drop drop exit then
  >r  r@ - i-len !  dup r@ + i-data !
  dup tcp-sport + n16@ i-sport !  dup tcp-dport + n16@ i-dport !
  dup tcp-seq + n32@ i-seq !  dup tcp-ack + n32@ i-ack !  dup tcp-window + n16@ i-wnd !
  f-syn i-flag? if  dup r@ options-mss  then
  drop r> drop
  find-conn ?dup if  segment-in exit  then
  f-syn i-flag?  f-ack i-flag? 0= and  i-dport @ listener-of 0<> and if
    room? if open-conn then exit                    \ beyond the caps: drop it, they will retry
  then
  refuse ;
' tcp-in proto-tcp ip-handler!

\ ---- Timers, run by the network task: retransmission and TIME-WAIT

: unsend-fin  ( conn -- )  \ our FIN must go again: back to the state before it went
  dup c.flags @ fin-sent invert and over c.flags !
  dup c.state @ fin-wait-1 = if  established swap c.state ! exit  then
  close-wait swap c.state ! ;

: retransmit  ( conn -- )  \ from the oldest unacknowledged byte, with a longer timeout
  dup c.retries @
  over c.state @ syn-received = if max-syn-retries @ else max-retries then
  < 0= if                                           \ give up
    dup dup snd-nxt f-rst control-out  release-conn exit
  then
  1 over c.retries +!
  dup c.rto @ 2* max-rto min over c.rto !
  0 over c.rexmit !
  dup c.state @ syn-received = if
    dup dup c.iss @ f-syn f-ack or control-out  arm-rexmit exit
  then
  dup c.snd-wnd @ 0= if  1 over c.snd-wnd !  then  \ probe a closed window
  dup c.tx-acked @ over c.tx-sent !
  dup fin-sent flag?  over fin-acked flag? 0= and if dup unsend-fin then
  tcp-output ;

: abort-connection  ( conn -- )  \ reset it now, whatever is queued
  dup c.state @ closed = if drop exit then
  dup dup snd-nxt f-rst control-out  release-conn ;

\ A closed connection's time is up: the end of TIME-WAIT or FIN-WAIT-2, or of
\ its linger time, if the other end would not take what was queued.
: timed-out  ( conn -- )
  dup c.state @  dup time-wait =  swap fin-wait-2 = or if  release-conn exit  then
  abort-connection ;

: tcp-timers  ( -- )
  conns @ begin ?dup while
    dup c.link @ swap                               ( next conn )
    dup c.rexmit @ ?dup if  expired? if dup retransmit then  then
    dup c.state @ closed <> if                      \ not just released by RETRANSMIT
      dup c.timeout @ ?dup if  expired? if dup timed-out then  then
    then
    drop
  repeat ;

\ ---- For the application. Words that wait sleep until the network task wakes
\ them, or until the task's IO-TIMEOUT runs out: then they throw -273, and a
\ send that made no progress for that long first resets the connection. A
\ connection must not be used after CLOSE-CONNECTION.

-273 message: timed out
user io-timeout                 \ ms a word may wait on the other end; 0: for ever
user io-until                   \ when the current wait ends, or 0
user cur-conn                   \ the connection SEND or GET-LINE is working on
60000 constant linger-ms        \ how long a closed connection may take to send what is queued

: io-start  ( -- )  io-timeout @ ?dup if deadline else 0 then io-until ! ;
: io-wait   ( -- )  \ sleep until woken; throw -273 if the time is up
  up@ cur-conn @ c.owner !
  io-until @ ?dup if  dup expired? if drop -273 throw then  stop-until  else  stop  then ;

: open?  ( conn -- flag )  \ we can still send on it
  dup c.state @  dup established =  swap close-wait = or  swap fin-queued flag? 0= and ;

\ Queue data on cur-conn, sending only when we must wait for room. Throws -269
\ once the connection is closed.
: (send)  ( addr len -- )
  io-start
  begin dup while
    cur-conn @ open? 0= if 2drop -269 throw then
    cur-conn @ tx-room ?dup 0= if
      cur-conn @ tcp-output
      ['] io-wait catch ?dup if  cur-conn @ abort-connection throw  then
    else
      io-start                                      \ progress: the time starts again
      over min                                      ( addr len n )
      dup 0 ?do  2 pick i + c@  cur-conn @ c.tx-queued @ i + /tx 1- and  cur-conn @ c.tx + c!  loop
      dup cur-conn @ c.tx-queued +!
      /string
    then
  repeat 2drop ;

create crlf  13 c, 10 c,
: send       ( addr len conn -- )  cur-conn !  (send)  cur-conn @ tcp-output ;
: send-line  ( addr len conn -- )  \ the line and CR LF, in one segment if they fit
  cur-conn !  (send)  crlf 2 (send)  cur-conn @ tcp-output ;

: line-length  ( conn -- n | -1 )  \ unread bytes before the first line feed
  dup rx-unread 0 ?do
    dup dup c.rx-out @ i + rx@ 10 = if  drop i unloop exit  then
  loop drop -1 ;
: take  ( addr n -- )  \ copy n unread bytes of cur-conn to addr
  0 ?do  cur-conn @ dup c.rx-out @ i + rx@  over i + c!  loop drop ;
: consumed  ( n -- )  \ n bytes are read: if the window had nearly shut, say it is open
  cur-conn @ rx-room our-mss <  swap cur-conn @ c.rx-out +!
  cur-conn @ rx-room our-mss < 0= and if  cur-conn @ dup ack-now flag+ tcp-output  then ;
: strip-cr  ( addr len -- len' )  dup if  2dup + 1- c@ 13 = if 1- then  then nip ;

\ Read a line into addr, without its CR LF, waiting for one. A line longer than
\ max is cut short. -1 once the other end has finished and nothing is left.
: get-line  ( addr max conn -- len | -1 )
  cur-conn !  io-start
  begin
    cur-conn @ line-length  dup 0< 0= if
      >r  r@ min  2dup take  r> 1+ consumed  strip-cr exit
    then drop
    cur-conn @ rx-unread over < 0= if  2dup take  dup consumed  nip exit  then
    cur-conn @ fin-received flag?  cur-conn @ c.state @ closed = or if
      cur-conn @ rx-unread ?dup if  min 2dup take  dup consumed  nip  else  2drop -1  then exit
    then
    io-wait
  again ;

\ Send what is queued, then a FIN; then let it go. If that has not finished
\ within LINGER-MS, the connection is reset.
: close-connection  ( conn -- )
  dup app-closed flag+
  dup c.state @ closed = if  free-conn exit  then
  linger-ms deadline over c.timeout !
  dup fin-queued flag+  tcp-output ;

: .tcp  ( -- )  \ connections live and pooled
  ." connections " conns @ count-list (.) type
  ." , pooled " free-conns @ count-list (.) type ;

