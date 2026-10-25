\ virtio.fs: the virtio-mmio transport, version 2 (virtio 1.x), polled.
\ QEMU's virt machine has 32 transports from $0a000000, $200 apart. Devices are
\ attached with "-device virtio-<type>-device"; "-global
\ virtio-mmio.force-legacy=false" selects version 2. Shared by the virtio
\ device drivers.

\ Transport registers, as offsets from a device's base address
$000 constant vm-magic                \ "virt"
$004 constant vm-version              \ 2 for virtio 1.x
$008 constant vm-device-id            \ 1 network, 2 block
$010 constant vm-features             \ offered by the device, 32 bits at a time
$014 constant vm-features-sel
$020 constant vm-driver-features      \ accepted by the driver
$024 constant vm-driver-features-sel
$030 constant vm-queue-sel
$034 constant vm-queue-num-max
$038 constant vm-queue-num
$044 constant vm-queue-ready
$050 constant vm-queue-notify
$070 constant vm-status
$080 constant vm-queue-desc           \ 64-bit physical addresses of the queue parts
$090 constant vm-queue-driver         \ the "available" ring
$0a0 constant vm-queue-device         \ the "used" ring
$100 constant vm-config               \ device-specific configuration

$0a000000 constant virtio-mmio-base
$74726976 constant virtio-magic

\ Device status bits
1 constant st-acknowledge
2 constant st-driver
4 constant st-driver-ok
8 constant st-features-ok

-261 message: virtio device refused to start

: vm@    ( base reg -- u )  + l@ ;
: vm!    ( u base reg -- )  + l! ;
: vm64!  ( u base reg -- )  + >r  dup $ffffffff and r@ l!  32 rshift r> 4 + l! ;

: virtio-find  ( device-id -- base | 0 )  \ the first transport holding that device
  32 0 do
    virtio-mmio-base i $200 * +
    dup vm-magic vm@ virtio-magic =
    over vm-version vm@ 2 = and
    over vm-device-id vm@ 3 pick = and
    if nip unloop exit then drop
  loop drop 0 ;

: status+    ( base bits -- )  over vm-status vm@ or  swap vm-status vm! ;
: features@  ( base sel -- u )  over vm-features-sel vm!  vm-features vm@ ;
: features!  ( u base sel -- )  over vm-driver-features-sel vm!  vm-driver-features vm! ;

\ Reset the device and negotiate features: VERSION_1, plus whichever of the
\ wanted low 32 feature bits the device offers. Returns the bits accepted.
: virtio-start  ( base wanted -- accepted )
  over 0 swap vm-status vm!
  over st-acknowledge st-driver or status+
  over 0 features@ and
  over 1 features@ 1 and 0= if -261 throw then
  2dup swap 0 features!  1 2 pick 1 features!
  over st-features-ok status+
  over vm-status vm@ st-features-ok and 0= if -261 throw then
  nip ;
: virtio-ready  ( base -- )  st-driver-ok status+ ;

\ ---- Split virtqueues, one page each: descriptors at 0, the available ring at
\ 128, the used ring at 256, and the last used index we have seen at 512.

8 constant vq-size
1 constant d-next                     \ descriptor flags: the chain continues
2 constant d-write                    \ the device writes this buffer

: new-vq     ( -- vq )  here 4095 + -4096 and dp !  here 4096 allot  dup 4096 0 fill ;
: vq-desc    ( vq i -- addr )  16 * + ;
: vq-avail   ( vq -- addr )  128 + ;
: vq-used    ( vq -- addr )  256 + ;
: vq-seen    ( vq -- addr )  512 + ;

\ Fill descriptor i: buffer, length, flags, next descriptor in the chain.
: desc!  ( addr len flags next vq i -- )
  vq-desc >r  r@ 14 + w!  r@ 12 + w!  r@ 8 + l!  >phys r> ! ;

: virtio-queue  ( base vq n -- )  \ give the device queue n, using vq
  2 pick vm-queue-sel vm!
  over vm-queue-num-max vm@ vq-size < if -261 throw then
  vq-size 2 pick vm-queue-num vm!
  dup >phys 2 pick vm-queue-desc vm64!
  dup vq-avail >phys 2 pick vm-queue-driver vm64!
  vq-used >phys over vm-queue-device vm64!
  1 swap vm-queue-ready vm! ;

\ Offer the chain starting at descriptor head, and ring queue n's doorbell.
: vq-submit  ( head vq base n -- )
  2swap  dup vq-avail 2 + w@ >r                    ( base n head vq )
  r@ vq-size 1- and 2* 4 + over vq-avail + rot swap w!
  dmb                                              \ the ring entry, then the index
  r> 1+ swap vq-avail 2 + w!
  dsb                                              \ all of it, then the doorbell
  swap vm-queue-notify vm! ;

\ Wait until the device has used one more chain. Polls for now: tasks and a
\ timeout arrive with the timer (milestone 5).
: vq-wait  ( vq -- )
  dup vq-seen @ 1+ $ffff and >r
  begin dup vq-used 2 + w@ r@ = until
  r> swap vq-seen !  dmb ;
