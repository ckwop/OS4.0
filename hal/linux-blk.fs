\ linux-blk.fs: the block HAL for the hosted build: disk image files, named by
\ the program's first argument as a comma-separated list, reached through Linux
\ system calls. Disks are numbered from 0 in that order; the layers above tell
\ them apart by what is on them, never by number.
\   #disks     ( -- n )             disks opened
\   blk-count  ( disk -- u )        size in 1 KiB blocks; 0 if there is no such disk
\   blk-read   ( addr u disk -- )   block u into the 1 KiB at addr
\   blk-write  ( addr u disk -- )   the 1 KiB at addr to block u
\   blk-flush  ( disk -- )          make completed writes durable

56 constant sys-openat
62 constant sys-lseek
67 constant sys-pread64
68 constant sys-pwrite64
82 constant sys-fsync
-100 constant at-fdcwd
0 constant o-rdonly
2 constant o-rdwr
2 constant seek-end
4 constant max-disks

: argc  ( -- n )  args @ ;
: arg   ( n -- c-addr | 0 )  dup argc < if 1+ cells args + @ else drop 0 then ;
: zlen  ( c-addr -- u )  0 begin 2dup + c@ while 1+ repeat nip ;

create disk-fds    max-disks cells allot
create disk-sizes  max-disks cells allot
create disk-names  256 allot          \ the first argument, each name ending in a zero
variable #found   -1 #found !         \ disks opened; -1 until the first look

: sys-open  ( c-addr flags -- fd )  at-fdcwd -rot 0 sys-openat syscall ;
: open-disk  ( c-addr -- )  \ read-write if we may, else read-only
  #found @ max-disks < 0= if drop exit then
  dup o-rdwr sys-open  dup 0< if  drop o-rdonly sys-open  else nip then
  dup 0< if drop exit then
  dup #found @ cells disk-fds + !
  0 seek-end 0 sys-lseek syscall 10 rshift  #found @ cells disk-sizes + !
  1 #found +! ;

: disks-open  ( -- )  \ open every image named, once
  #found @ 0< 0= if exit then  0 #found !
  1 arg ?dup 0= if exit then
  dup zlen 255 min  tuck disk-names swap cmove  disk-names + >r  0 r@ c!
  r@ disk-names ?do  i c@ [char] , = if 0 i c! then  loop
  disk-names begin dup r@ u< while  dup c@ if dup open-disk then  dup zlen + 1+  repeat
  drop r> drop ;

: #disks     ( -- n )  disks-open #found @ ;
: blk-count  ( n -- u )  dup #disks u< if cells disk-sizes + @ else drop 0 then ;
: disk-fd    ( n -- fd )  cells disk-fds + @ ;
: blk-read   ( addr u n -- )
  dup #disks u< 0= if -33 throw then
  disk-fd -rot 1024 swap 10 lshift sys-pread64 syscall 1024 <> if -33 throw then ;
: blk-write  ( addr u n -- )
  dup #disks u< 0= if -34 throw then
  disk-fd -rot 1024 swap 10 lshift sys-pwrite64 syscall 1024 <> if -34 throw then ;
: blk-flush  ( n -- )
  dup #disks u< 0= if -34 throw then
  disk-fd 0 0 0 sys-fsync syscall if -34 throw then ;
