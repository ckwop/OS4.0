\ net/arp.fs: ARP, which maps IPv4 addresses on the local network to MAC
\ addresses. Answers requests for our address, learns from every ARP packet
\ for us (and from IP packets, in ip.fs), and asks when a MAC is not known.

\ ARP packet fields, from the start of the packet
0 constant arp-htype
2 constant arp-ptype
4 constant arp-hlen
5 constant arp-plen
6 constant arp-oper            \ 1 request, 2 reply
8 constant arp-sha             \ sender MAC and IP
14 constant arp-spa
18 constant arp-tha            \ target MAC and IP
24 constant arp-tpa
28 constant /arp

\ ---- The cache: 8 entries of IP address and MAC, replaced round robin

8 constant #arp
create arp-cache  #arp 2 cells * allot   arp-cache #arp 2 cells * 0 fill
variable arp-next
variable arps-answered

: arp-entry  ( i -- addr )  2 cells * arp-cache + ;
: arp-find   ( ip -- mac | 0 )
  #arp 0 do  dup i arp-entry @ = if  drop i arp-entry cell+ unloop exit  then  loop
  drop 0 ;
: arp-learn  ( mac ip -- )  \ not for a group MAC, nor an address no host has
  dup 0=  over bad-source? or  2 pick group-mac? or if 2drop exit then
  dup arp-find ?dup if
    nip
  else
    arp-next @  dup 1+ #arp mod arp-next !
    arp-entry tuck !  cell+
  then 6 cmove ;

\ ---- Sending. ARP packets are built in their own frame, so asking for a MAC
\ never disturbs a packet being built in tx-frame.

create arp-frame 64 allot
: arp-out  ( -- addr )  arp-frame /eth + ;
: arp-header  ( oper -- )  \ an ARP packet from us
  1 arp-out arp-htype + n16!  type-ipv4 arp-out arp-ptype + n16!
  6 arp-out arp-hlen + c!  4 arp-out arp-plen + c!
  arp-out arp-oper + n16!
  net-mac arp-out arp-sha + 6 cmove  my-ip @ arp-out arp-spa + n32! ;

: (arp-request)  ( ip -- )
  1 arp-header  arp-out arp-tha + 6 0 fill  arp-out arp-tpa + n32!
  arp-frame broadcast-mac type-arp /arp eth-send ;
: arp-request  ( ip -- )  \ who has ip? Broadcast.
  ['] (arp-request) tx-lock locked ;

: (arp-reply)  ( request -- )
  2 arp-header
  dup arp-sha + arp-out arp-tha + 6 cmove
  dup arp-spa + n32@ arp-out arp-tpa + n32!
  arp-frame swap arp-sha + type-arp /arp eth-send
  1 arps-answered +! ;
: arp-reply  ( request -- )  \ answer the request at that address
  ['] (arp-reply) tx-lock locked ;

: arp-in  ( packet len -- )  \ an ARP packet; ignore any not about us
  /arp < if drop exit then
  dup arp-htype + n16@ 1 =  over arp-ptype + n16@ type-ipv4 = and
  over arp-hlen + c@ 6 = and  over arp-plen + c@ 4 = and 0= if drop exit then
  dup arp-tpa + n32@ my-ip @ <> if drop exit then
  dup arp-sha + over arp-spa + n32@ arp-learn
  dup arp-oper + n16@ 1 = if arp-reply else drop then ;

\ ---- Finding the MAC to send to

: on-link?  ( ip -- flag )  my-ip @ xor netmask @ and 0= ;
: next-hop  ( ip -- ip' )  dup on-link? 0= if drop gateway @ then ;
: resolve   ( ip -- mac | 0 )  \ 0 if not yet known; an ARP request has then gone out
  dup broadcast-ip = if drop broadcast-mac exit then
  next-hop  dup arp-find ?dup if nip exit then
  arp-request 0 ;
