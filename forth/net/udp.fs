\ net/udp.fs: UDP. A datagram for a bound port goes to that port's handler;
\ one for any other port is answered with ICMP port unreachable.

0 constant udp-sport
2 constant udp-dport
4 constant udp-length          \ header and data
6 constant udp-checksum        \ over a pseudo-header, the header and the data; 0: none
8 constant /udp
1472 constant udp-max          \ the most data that fits a 1500-byte IP packet

-265 message: datagram too large
-266 message: no free UDP port slot


\ ---- Ports. Handlers take ( data len -- ) and run in the network task; while
\ one runs, UDP-PEER-IP, UDP-PEER-PORT and UDP-REPLY refer to its datagram.

16 constant #udp-ports
create udp-ports  #udp-ports 2 cells * allot   udp-ports #udp-ports 2 cells * 0 fill
: udp-slot  ( i -- addr )  2 cells * udp-ports + ;   \ port, then handler; port 0: free
: udp-find  ( port -- slot | 0 )
  #udp-ports 0 do  dup i udp-slot @ = if  drop i udp-slot unloop exit  then  loop
  drop 0 ;
: udp-bind    ( xt port -- )  \ datagrams to port go to xt
  dup udp-find ?dup 0= if  0 udp-find dup 0= if -266 throw then  then
  tuck !  cell+ ! ;
: udp-unbind  ( port -- )  udp-find ?dup if 0 swap ! then ;

\ ---- Receiving

variable rx-udp                 \ the datagram being handled
: udp-peer-ip     ( -- ip )  ip-source ;
: udp-peer-port   ( -- port )  rx-udp @ udp-sport + n16@ ;
: udp-local-port  ( -- port )  rx-udp @ udp-dport + n16@ ;

: udp-in  ( segment len -- )
  over rx-udp !
  over udp-length + n16@  dup /udp <  over 3 pick > or if  2drop drop exit  then
  nip                                                    ( segment ulen )
  over udp-checksum + n16@ if
    ip-source  rx-ip ip-dst + n32@  2 pick proto-udp pseudo-sum  2 pick 2 pick sum16 fold
    if 2drop exit then
  then
  over udp-dport + n16@ udp-find ?dup if
    cell+ @ >r  /udp - swap /udp + swap  r> execute
  else
    2drop port-unreachable unreachable
  then ;
' udp-in proto-udp ip-handler!

\ ---- Sending

: tx-udp  ( -- addr )  tx-frame ip-payload + ;
variable udp-to

: (udp-send)  ( data len port dst-ip dst-port -- flag )
  tx-udp udp-dport + n16!  udp-to !  tx-udp udp-sport + n16!
  dup udp-max > if 2drop -265 throw then
  dup >r  tx-udp /udp + swap cmove
  r> /udp +  dup tx-udp udp-length + n16!
  0 tx-udp udp-checksum + n16!
  my-ip @ udp-to @ 2 pick proto-udp pseudo-sum  tx-udp 2 pick sum16 fold
  ?dup 0= if $ffff then  tx-udp udp-checksum + n16!
  proto-udp udp-to @ ip-send ;

\ Send len bytes from data, from our port to dst-port at dst-ip. False if the
\ destination's MAC is not known yet: an ARP request has gone out; try again.
: udp-send  ( data len port dst-ip dst-port -- flag )  ['] (udp-send) tx-lock locked ;

: udp-reply  ( data len -- flag )  \ to the sender of the datagram being handled
  udp-local-port udp-peer-ip udp-peer-port udp-send ;

\ ---- Echo (RFC 862): every datagram to port 7 comes straight back.

7 constant echo-port
: echo  ( data len -- )  udp-reply drop ;
: echo-service  ( -- )  ['] echo echo-port udp-bind ;
