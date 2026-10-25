\ linux-blk.fs: the block HAL for the hosted build: a disk image file, named by
\ the program's first argument, reached through Linux system calls.
\   blk-count  ( -- u )       size in 1 KiB blocks; 0 if there is no disk
\   blk-read   ( addr u -- )  block u into the 1 KiB at addr
\   blk-write  ( addr u -- )  the 1 KiB at addr to block u
\   blk-flush  ( -- )         make completed writes durable

56 constant sys-openat
62 constant sys-lseek
67 constant sys-pread64
68 constant sys-pwrite64
82 constant sys-fsync
-100 constant at-fdcwd
2 constant o-rdwr
2 constant seek-end

: argc  ( -- n )  args @ ;
: arg   ( n -- c-addr | 0 )  dup argc < if 1+ cells args + @ else drop 0 then ;

variable disk-fd   -1 disk-fd !
variable #disk-blocks

: blk-open  ( -- )  \ open the image, once
  disk-fd @ 0< 0= if exit then
  1 arg ?dup 0= if exit then
  at-fdcwd swap o-rdwr 0 sys-openat syscall
  dup 0< if drop exit then
  dup disk-fd !
  0 seek-end 0 sys-lseek syscall 10 rshift #disk-blocks ! ;

: blk-count  ( -- u )  blk-open  disk-fd @ 0< if 0 else #disk-blocks @ then ;
: blk-read   ( addr u -- )
  >r disk-fd @ swap 1024 r> 10 lshift sys-pread64 syscall 1024 <> if -33 throw then ;
: blk-write  ( addr u -- )
  >r disk-fd @ swap 1024 r> 10 lshift sys-pwrite64 syscall 1024 <> if -34 throw then ;
: blk-flush  ( -- )  disk-fd @ 0 0 0 sys-fsync syscall if -34 throw then ;
