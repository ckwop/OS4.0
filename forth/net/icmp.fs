\ net/icmp.fs: ICMP echo. Answers pings, and PING sends them.

0 constant icmp-type           \ 8 echo request, 0 echo reply
1 constant icmp-code
2 constant icmp-checksum
4 constant icmp-ident
6 constant icmp-seq
8 constant /icmp-echo          \ the echo header; data follows

variable echoes-answered

: tx-icmp  ( -- addr )  tx-frame ip-payload + ;
: icmp-send  ( len dst -- flag )  \ an ICMP message of len bytes, built at tx-icmp
  0 tx-icmp icmp-checksum + n16!
  over tx-icmp swap checksum  tx-icmp icmp-checksum + n16!
  proto-icmp swap ip-send ;

: echo-reply  ( message len -- )  \ the same identifier, sequence and data, back
  dup >r  tx-icmp swap cmove  0 tx-icmp icmp-type + c!
  r> ip-source icmp-send if 1 echoes-answered +! then ;

\ ---- Our own pings

$4f53 constant ping-ident
variable pong                   \ sequence number of the last reply to us
: ping-data  ( -- addr u )  s" OS 4.0 ping: 32 bytes of data..." ;

: echo-in  ( message len -- )  \ a reply: note it if it answers our PING
  drop  dup icmp-ident + n16@ ping-ident = if  icmp-seq + n16@ pong !  else drop then ;

: icmp-in  ( message len -- )
  2dup checksum if 2drop exit then
  over icmp-type + c@  dup 8 = if drop echo-reply exit then
  0= if echo-in else 2drop then ;
' icmp-in proto-icmp ip-handler!

: send-echo  ( seq ip -- flag )
  >r  8 tx-icmp icmp-type + c!  0 tx-icmp icmp-code + c!
  ping-ident tx-icmp icmp-ident + n16!  tx-icmp icmp-seq + n16!
  ping-data tx-icmp /icmp-echo + swap cmove
  ping-data nip /icmp-echo +  r> icmp-send ;

: send-ping  ( seq ip -- )  \ keep trying for a second: the first try may only send an ARP request
  1000 deadline >r
  begin 2dup send-echo 0= while  r@ expired? if 2drop r> drop exit then  10 ms  repeat
  2drop r> drop ;
: wait-pong  ( seq -- flag )  \ up to a second
  1000 deadline >r
  begin  dup pong @ = if drop r> drop true exit then
         r@ expired? if drop r> drop false exit then  10 ms  again ;

: ping  ( ip -- )  \ three echo requests
  net-up? 0= if -264 throw then
  0 pong !
  4 1 do
    i over send-ping
    i wait-pong if  ." reply " i (.) type ."  from " dup .ip  else  ." no reply " i (.) type  then cr
  loop drop ;
