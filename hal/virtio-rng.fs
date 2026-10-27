\ virtio-rng.fs: the entropy HAL as a virtio-rng device on the virtio-mmio
\ transport ("-device virtio-rng-device"; QEMU feeds it from the host).
\   entropy  ( addr u -- )  fill addr with u bytes of hardware randomness
\ One task at a time: random.fs is its only caller and holds a lock.

4 constant virtio-rng-id
-272 message: no entropy source

variable rng-base                     \ the device, once started; 0 until then
4 new-vq constant rng-vq

: rng-open  ( -- )  \ find and start the device, once
  rng-base @ if exit then
  virtio-rng-id virtio-find ?dup 0= if exit then
  dup 0 virtio-start drop
  dup rng-vq 0 virtio-queue
  dup virtio-ready
  rng-base ! ;

: entropy  ( addr u -- )  \ the device may give fewer bytes than asked: ask again
  rng-open  rng-base @ 0= if -272 throw then
  begin dup while
    2dup d-write 0 rng-vq 0 desc!
    0 rng-vq rng-base @ 0 vq-submit
    rng-vq vq-wait-len  over min /string
  repeat 2drop ;
