\ net/eth.fs: what the network stack shares: network byte order, addresses and
\ their notation, this machine's configuration, Ethernet framing, and the
\ Internet checksum. Frames come and go through the network HAL (hal/).

-264 message: no network interface

\ ---- Network byte order: most significant byte first

: n16@  ( addr -- u )  dup c@ 8 lshift  swap 1+ c@ or ;
: n16!  ( u addr -- )  over 8 rshift over c!  1+ c! ;
: n32@  ( addr -- u )  dup n16@ 16 lshift  swap 2 + n16@ or ;
: n32!  ( u addr -- )  over 16 rshift over n16!  2 + n16! ;

\ ---- Addresses. An IPv4 address is a number; ip 10.0.2.15 reads one.

: .ip  ( u -- )
  4 0 do  dup 24 i 8 * - rshift 255 and (.) type  i 3 < if [char] . emit then  loop drop ;
: ip   ( "a.b.c.d" -- u )
  parse-name  0 0 2swap                                   ( ip octet addr u )
  0 ?do
    dup i + c@  dup [char] . = if
      drop >r  swap 8 lshift +  0  r>
    else
      [char] 0 -  rot 10 * +  swap
    then
  loop drop  swap 8 lshift + ;
: .mac  ( addr -- )
  base @ >r hex
  6 0 do  dup i + c@ 0 <# # # #> type  i 5 < if [char] : emit then  loop drop
  r> base ! ;

\ ---- This machine. QEMU's user networking puts the gateway at 10.0.2.2.

variable my-ip      ip 10.0.2.15 my-ip !
variable netmask    ip 255.255.255.0 netmask !
variable gateway    ip 10.0.2.2 gateway !
$ffffffff constant broadcast-ip

\ ---- Ethernet frames: destination MAC, source MAC, type, then the payload.

0 constant eth-dst
6 constant eth-src
12 constant eth-type
14 constant /eth
$0800 constant type-ipv4
$0806 constant type-arp

create rx-frame 2048 allot             \ the frame being handled
create tx-frame 2048 allot             \ the frame being built
create broadcast-mac  $ff c, $ff c, $ff c, $ff c, $ff c, $ff c,
variable frames-in
variable frames-out

: eth-send  ( frame mac type len -- )  \ fill in the header; send the frame with len bytes of payload
  >r  2 pick eth-type + n16!
  over eth-dst + 6 cmove
  net-mac over eth-src + 6 cmove
  r> /eth + net-send  1 frames-out +! ;

\ ---- The Internet checksum: the one's complement of the one's complement sum
\ of 16-bit words. A packet whose checksum field is right sums to 0. SUM16 and
\ FOLD let a checksum cover parts that are not in one piece (UDP's pseudo-header).

: sum16  ( sum addr u -- sum' )  \ add the bytes as 16-bit words, padding an odd one
  begin dup 1 > while  over n16@ >r rot r> + -rot  2 /string  repeat
  if c@ 8 lshift + else drop then ;
: fold   ( sum -- u16 )  \ the checksum of a sum
  begin dup 16 rshift while  dup $ffff and swap 16 rshift +  repeat
  invert $ffff and ;
: checksum  ( addr u -- u16 )  0 -rot sum16 fold ;
