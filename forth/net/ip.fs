\ net/ip.fs: IPv4. Checks incoming packets and hands each to the handler for
\ its protocol; builds the header for outgoing ones. No fragments, no options
\ sent, no routing beyond "on this network, or via the gateway".

\ Header fields, from the start of the header
0 constant ip-ver-ihl
2 constant ip-length           \ the whole packet
4 constant ip-ident
6 constant ip-fragment         \ flags and fragment offset
8 constant ip-ttl
9 constant ip-protocol
10 constant ip-checksum
12 constant ip-src
16 constant ip-dst
20 constant /ip                \ the header we send: no options

1 constant proto-icmp
6 constant proto-tcp
17 constant proto-udp

\ ---- Protocol handlers: ( payload len -- ), by protocol number

create ip-handlers  256 cells allot   ip-handlers 256 cells 0 fill
: ip-handler!  ( xt protocol -- )  cells ip-handlers + ! ;
variable 'no-protocol  ' 2drop 'no-protocol !   \ ( payload len -- ) for the rest; icmp.fs replies

: rx-ip  ( -- addr )  rx-frame /eth + ;         \ the packet being handled
: tx-ip  ( -- addr )  tx-frame /eth + ;         \ the packet being built
/eth /ip + constant ip-payload                   \ where a payload goes in tx-frame
: ip-source  ( -- ip )  rx-ip ip-src + n32@ ;    \ who sent the packet being handled

\ The pseudo-header's share of a UDP or TCP checksum: both addresses, the
\ protocol and the segment's length.
: pseudo-sum  ( src dst len protocol -- sum )
  +  swap dup 16 rshift swap $ffff and + +
  swap dup 16 rshift swap $ffff and + + ;

: ip-in  ( len -- )  \ an IPv4 packet of up to len bytes in rx-frame
  rx-ip >r
  r@ ip-ver-ihl + c@  dup 4 rshift 4 <> if  2drop r> drop exit  then
  15 and 4 *                                     ( len ihl )
  dup /ip < if  2drop r> drop exit  then
  r@ over checksum if  2drop r> drop exit  then
  r@ ip-length + n16@  rot over < if  2drop r> drop exit  then   ( ihl total )
  r@ ip-fragment + n16@ $3fff and if  2drop r> drop exit  then
  r@ ip-dst + n32@  dup my-ip @ =  swap broadcast-ip = or 0= if  2drop r> drop exit  then
  ip-source dup on-link? if  rx-frame eth-src + swap arp-learn  else drop then
  over - swap r@ + swap                          ( payload len )
  r> ip-protocol + c@ cells ip-handlers + @ ?dup if execute else 'no-protocol @ execute then ;

\ Send len bytes of payload, already at ip-payload in tx-frame, to dst. False if
\ dst's MAC is not known yet: an ARP request has gone out instead; try again.
variable ip-next-id
: ip-send  ( len protocol dst -- flag )
  dup resolve ?dup 0= if  2drop drop false exit  then  >r
  tx-ip ip-dst + n32!  tx-ip ip-protocol + c!          ( len )
  $45 tx-ip ip-ver-ihl + c!  0 tx-ip 1+ c!
  dup /ip + tx-ip ip-length + n16!
  1 ip-next-id +!  ip-next-id @ tx-ip ip-ident + n16!
  0 tx-ip ip-fragment + n16!  64 tx-ip ip-ttl + c!
  my-ip @ tx-ip ip-src + n32!
  0 tx-ip ip-checksum + n16!  tx-ip /ip checksum tx-ip ip-checksum + n16!
  tx-frame swap r> swap type-ipv4 swap /ip + eth-send
  true ;
