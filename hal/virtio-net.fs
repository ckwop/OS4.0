\ virtio-net.fs: the network interface as a virtio-net device on the
\ virtio-mmio transport. Provides the network HAL that forth/net uses:
\   net-up?   ( -- flag )      there is a network interface
\   net-mac   ( -- addr )      its 6-byte MAC address
\   net-send  ( addr len -- )  send one Ethernet frame
\   net-poll  ( addr -- len )  copy a received frame to addr (room for 2 KiB); 0 if none
\ Receive buffers wait on queue 0; frames go out one at a time on queue 1.
\ Every buffer starts with the 12-byte virtio-net header.

1 constant virtio-net-id
1 5 lshift constant net-f-mac         \ VIRTIO_NET_F_MAC: the device has a MAC address
12 constant /net-header
2048 constant /net-buf

variable net-base                     \ the device, once started; 0 until then
64 constant #rx-bufs                  \ frames that can arrive between two polls
#rx-bufs new-vq constant rx-vq
8 new-vq constant tx-vq
create rx-bufs  #rx-bufs /net-buf * allot
create tx-buf   /net-buf allot
create mac 6 allot

: rx-buf   ( i -- addr )  /net-buf * rx-bufs + ;
: rx-post  ( i -- )  \ give receive buffer i to the device
  dup rx-buf /net-buf d-write 0 rx-vq 5 pick desc!
  rx-vq net-base @ 0 vq-submit ;

: net-open  ( -- )  \ find and start the device, once
  net-base @ if exit then
  virtio-net-id virtio-find ?dup 0= if exit then
  dup net-f-mac virtio-start net-f-mac and 0= if -261 throw then
  6 0 do  dup vm-config + i + c@  mac i + c!  loop
  dup rx-vq 0 virtio-queue
  dup tx-vq 1 virtio-queue
  dup virtio-ready
  net-base !
  #rx-bufs 0 do i rx-post loop ;

: net-up?   ( -- flag )  net-open  net-base @ 0<> ;
: net-mac   ( -- addr )  mac ;

: net-send  ( addr len -- )
  net-up? 0= if 2drop exit then
  tx-buf /net-header 0 fill
  >r  tx-buf /net-header + r@ cmove
  tx-buf r> /net-header + 0 0 tx-vq 0 desc!
  0 tx-vq net-base @ 1 vq-submit  tx-vq vq-wait ;

\ The id and length come from the device, so neither is trusted: a buffer we
\ never posted is ignored, and a length is held to the buffer.
: net-poll  ( addr -- len )
  net-up? 0= if drop 0 exit then
  rx-vq vq-used? 0= if drop 0 exit then
  rx-vq vq-take                                ( addr id len )
  over #rx-bufs u< 0= if  2drop drop 0 exit  then
  /net-header - 0 max  /net-buf /net-header - min >r
  tuck rx-buf /net-header + swap r@ cmove
  rx-post  r> ;
