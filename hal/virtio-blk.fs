\ virtio-blk.fs: disks as virtio-blk devices on the virtio-mmio transport.
\ Provides the block HAL; disks are numbered from 0 in transport order, and
\ the layers above tell them apart by what is on them, never by number:
\   #disks     ( -- n )             disks found
\   blk-count  ( disk -- u )        size in 1 KiB blocks; 0 if there is no such disk
\   blk-read   ( addr u disk -- )   block u into the 1 KiB at addr
\   blk-write  ( addr u disk -- )   the 1 KiB at addr to block u
\   blk-flush  ( disk -- )          make completed writes durable
\ One request at a time per disk, as a three-descriptor chain: header, data, status.

2 constant virtio-blk-id
1 9 lshift constant blk-f-flush       \ VIRTIO_BLK_F_FLUSH: the device caches writes
0 constant req-in
1 constant req-out
4 constant req-flush
4 constant max-disks

\ A disk: its transport, the features accepted, its size in blocks, its queue,
\ then room for a request header (16 bytes) and the device's status reply.
: d.base      ( d -- addr ) ;
: d.features  ( d -- addr )  cell+ ;
: d.blocks    ( d -- addr )  2 cells + ;
: d.vq        ( d -- addr )  3 cells + ;
: d.header    ( d -- addr )  4 cells + ;
: d.status    ( d -- addr )  6 cells + ;
7 cells constant /disk

create disks  max-disks /disk * allot
disks max-disks /disk * 0 fill
: disk  ( n -- d )  /disk * disks + ;
: make-queues  ( -- )  max-disks 0 do  8 new-vq i disk d.vq !  loop ;  \ 3 entries are enough
make-queues

variable #found   -1 #found !         \ disks started; -1 until the first look

: disk-start  ( base d -- )
  over blk-f-flush virtio-start over d.features !
  over over d.vq @ 0 virtio-queue
  over virtio-ready
  over vm-config vm@  2 pick vm-config 4 + vm@ 32 lshift or  1 rshift over d.blocks !
  d.base ! ;

: disks-open  ( -- )  \ find and start every virtio-blk device, once
  #found @ 0< 0= if exit then  0 #found !
  max-disks 0 do
    virtio-blk-id i virtio-nth ?dup if  i disk disk-start  1 #found +!  then
  loop ;

: #disks     ( -- n )  disks-open #found @ ;
: blk-count  ( n -- u )  dup #disks u< if disk d.blocks @ else drop 0 then ;

: blk-request  ( buf type sector d -- status )
  >r  r@ d.header 8 + !  dup r@ d.header l!  0 r@ d.header 4 + l!
  $ff r@ d.status c!
  r@ d.header 16 d-next 1 r@ d.vq @ 0 desc!
  dup req-flush = if
    2drop  r@ d.status 1 d-write 0 r@ d.vq @ 1 desc!
  else
    req-in = if d-write else 0 then d-next or  1024 swap 2 r@ d.vq @ 1 desc!
    r@ d.status 1 d-write 0 r@ d.vq @ 2 desc!
  then
  0 r@ d.vq @ r@ d.base @ 0 vq-submit  r@ d.vq @ vq-wait
  r> d.status c@ ;

: blk-read   ( addr u n -- )
  dup #disks u< 0= if -33 throw then  >r req-in swap 2* r> disk blk-request if -33 throw then ;
: blk-write  ( addr u n -- )
  dup #disks u< 0= if -34 throw then  >r req-out swap 2* r> disk blk-request if -34 throw then ;
: blk-flush  ( n -- )
  dup #disks u< 0= if -34 throw then  disk
  dup d.features @ blk-f-flush and if  >r 0 req-flush 0 r> blk-request if -34 throw then  else drop then ;
