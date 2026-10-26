\ virtio-blk.fs: the data disk as a virtio-blk device on the virtio-mmio
\ transport. Provides the block HAL that blocks.fs uses:
\   blk-count  ( -- u )       size in 1 KiB blocks; 0 if there is no disk
\   blk-read   ( addr u -- )  block u into the 1 KiB at addr
\   blk-write  ( addr u -- )  the 1 KiB at addr to block u
\   blk-flush  ( -- )         make completed writes durable
\ One request at a time, as a three-descriptor chain: header, data, status.

2 constant virtio-blk-id
1 9 lshift constant blk-f-flush       \ VIRTIO_BLK_F_FLUSH: the device caches writes
0 constant req-in
1 constant req-out
4 constant req-flush

variable blk-base                     \ the device, once started; 0 until then
variable blk-features
variable #disk-blocks
8 new-vq constant blk-vq              \ one request at a time needs only 3
create blk-header 16 allot            \ request type, reserved, sector
create blk-status 8 allot             \ the device's reply: 0 means done

: blk-open  ( -- )  \ find and start the device, once
  blk-base @ if exit then
  virtio-blk-id virtio-find ?dup 0= if exit then
  dup blk-f-flush virtio-start blk-features !
  dup blk-vq 0 virtio-queue
  dup virtio-ready
  dup vm-config vm@  over vm-config 4 + vm@ 32 lshift or  1 rshift #disk-blocks !
  blk-base ! ;

: blk-count  ( -- u )  blk-open  blk-base @ if #disk-blocks @ else 0 then ;

: blk-request  ( buf type sector -- status )
  blk-header 8 + !  dup blk-header l!  0 blk-header 4 + l!
  $ff blk-status c!
  blk-header 16 d-next 1 blk-vq 0 desc!
  dup req-flush = if
    2drop  blk-status 1 d-write 0 blk-vq 1 desc!
  else
    req-in = if d-write else 0 then d-next or  >r 1024 r> 2 blk-vq 1 desc!
    blk-status 1 d-write 0 blk-vq 2 desc!
  then
  0 blk-vq blk-base @ 0 vq-submit  blk-vq vq-wait
  blk-status c@ ;

: blk-read   ( addr u -- )  req-in swap 2* blk-request if -33 throw then ;
: blk-write  ( addr u -- )  req-out swap 2* blk-request if -34 throw then ;
: blk-flush  ( -- )
  blk-features @ blk-f-flush and if  0 req-flush 0 blk-request if -34 throw then  then ;
