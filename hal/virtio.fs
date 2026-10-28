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

: virtio-nth  ( device-id n -- base | 0 )  \ the transport holding the nth such device, from 0
  32 0 do
    virtio-mmio-base i $200 * +
    dup vm-magic vm@ virtio-magic =
    over vm-version vm@ 2 = and
    over vm-device-id vm@ 4 pick = and
    if  over 0= if nip nip unloop exit then  swap 1- swap  then drop
  loop 2drop 0 ;
: virtio-find  ( device-id -- base | 0 )  0 virtio-nth ;  \ the first transport holding that device

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

\ ---- Split virtqueues. A vq is five cells: its size (a power of two), the last
\ used index seen, and the addresses of its three parts, which follow: the
\ descriptor table (16 bytes each), the available ring and the used ring.

1 constant d-next                     \ descriptor flags: the chain continues
2 constant d-write                    \ the device writes this buffer

: vq-size    ( vq -- n )  @ ;
: vq-seen    ( vq -- addr )  cell+ ;
: vq-desc    ( vq i -- addr )  16 *  swap 2 cells + @ + ;
: vq-avail   ( vq -- addr )  3 cells + @ ;
: vq-used    ( vq -- addr )  4 cells + @ ;

: new-vq  ( n -- vq )  \ a virtqueue of n entries, zeroed
  align here >r  dup ,  0 , 0 , 0 , 0 ,
  here 15 + -16 and dp !
  here r@ 2 cells + !  dup 16 * allot           \ descriptors
  here r@ 3 cells + !  dup 2* 6 + allot         \ available ring: flags, index, entries, event
  here 3 + -4 and dp !
  here r@ 4 cells + !  8 * 6 + allot            \ used ring: flags, index, entries, event
  r@ 0 vq-desc  here over - 0 fill
  r> ;

\ Fill descriptor i: buffer, length, flags, next descriptor in the chain.
: desc!  ( addr len flags next vq i -- )
  vq-desc >r  r@ 14 + w!  r@ 12 + w!  r@ 8 + l!  >phys r> ! ;

: virtio-queue  ( base vq n -- )  \ give the device queue n, using vq
  2 pick vm-queue-sel vm!
  over vm-queue-num-max vm@  over vq-size < if -261 throw then
  dup vq-size 2 pick vm-queue-num vm!
  dup 0 vq-desc >phys 2 pick vm-queue-desc vm64!
  dup vq-avail >phys 2 pick vm-queue-driver vm64!
  vq-used >phys over vm-queue-device vm64!
  1 swap vm-queue-ready vm! ;

\ Offer the chain starting at descriptor head, and ring queue n's doorbell.
: vq-submit  ( head vq base n -- )
  2swap  dup vq-avail 2 + w@ >r                    ( base n head vq )
  r@ over vq-size 1- and 2* 4 + over vq-avail + rot swap w!
  dmb                                              \ the ring entry, then the index
  r> 1+ swap vq-avail 2 + w!
  dsb                                              \ all of it, then the doorbell
  swap vm-queue-notify vm! ;

\ The used ring: the device hands back chains, with the length it wrote.
: vq-used?  ( vq -- flag )  \ a used chain is waiting
  dup vq-used 2 + w@  swap vq-seen @ <> ;
: vq-take   ( vq -- id len )  \ the next used chain: its head and length
  dmb                                              \ the index, then the entry
  dup vq-seen @  dup 1+ $ffff and  2 pick vq-seen !
  over vq-size 1- and 8 * 4 +  swap vq-used +  dup l@ swap 4 + l@ ;

-263 message: a device did not respond in time
5000 constant device-timeout          \ ms

\ Wait for the device to use one more chain, letting other tasks run meanwhile.
\ Callers hold a lock for the queue (blocks-lock for the disk, tx-lock for the
\ network), so no other task can submit to it in between.
: vq-wait-len  ( vq -- len )  \ and the length the device wrote
  device-timeout deadline >r
  begin dup vq-used? 0= while  r@ expired? if  r> 2drop -263 throw  then  pause  repeat
  r> drop  vq-take nip ;
: vq-wait  ( vq -- )  vq-wait-len drop ;
