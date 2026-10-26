\ linux-net.fs: the network HAL for the hosted build. Ethernet frames travel as
\ UDP datagrams on 127.0.0.1, one frame each: the format of QEMU's "dgram"
\ network backend, so the same test peer serves both builds. The program's
\ second and third arguments are our port and the peer's port.
\   net-up?   ( -- flag )      there is a network interface
\   net-mac   ( -- addr )      its 6-byte MAC address
\   net-send  ( addr len -- )  send one Ethernet frame
\   net-poll  ( addr -- len )  copy a received frame to addr (room for 2 KiB); 0 if none

25 constant sys-fcntl
63 constant sys-read
64 constant sys-write
198 constant sys-socket
200 constant sys-bind
203 constant sys-connect
2 constant af-inet
2 constant sock-dgram
4 constant f-setfl
$800 constant o-nonblock

create mac  $52 c, $54 c, $00 c, $12 c, $34 c, $56 c,   \ as QEMU gives its first NIC
variable net-fd   -1 net-fd !

: cstr>u  ( c-addr -- u )  \ a decimal number in a zero-terminated string
  0 swap begin dup c@ ?dup while  [char] 0 -  rot 10 * +  swap 1+  repeat drop ;

create sockaddr 16 allot
: localhost  ( port -- addr )  \ a struct sockaddr_in for 127.0.0.1:port
  sockaddr 16 0 fill  af-inet sockaddr w!
  dup 8 rshift sockaddr 2 + c!  sockaddr 3 + c!
  127 sockaddr 4 + c!  1 sockaddr 7 + c!  sockaddr ;

: net-open  ( -- )  \ bind our port and connect to the peer's, once
  net-fd @ 0< 0= if exit then
  2 arg 0= 3 arg 0= or if exit then
  af-inet sock-dgram 0 0 sys-socket syscall  dup 0< if drop exit then
  dup 2 arg cstr>u localhost 16 0 sys-bind syscall if drop exit then
  dup 3 arg cstr>u localhost 16 0 sys-connect syscall if drop exit then
  dup f-setfl o-nonblock 0 sys-fcntl syscall drop
  net-fd ! ;

: net-up?   ( -- flag )  net-open  net-fd @ 0< 0= ;
: net-mac   ( -- addr )  mac ;
: net-send  ( addr len -- )
  net-up? 0= if 2drop exit then
  net-fd @ -rot 0 sys-write syscall drop ;
: net-poll  ( addr -- len )
  net-up? 0= if drop 0 exit then
  net-fd @ swap 2048 0 sys-read syscall  0 max ;
