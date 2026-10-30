\ files.fs: files on the app disk, read only (DECISIONS.md #99). The app disk
\ is a FAT16 or FAT32 volume labelled OS4APP, made with ordinary tools
\ (mkfs.fat and mcopy: see tools/app-disk.sh) and formatted whole, with no
\ partition table. The OS never writes it: what the OS writes goes in blocks on
\ the data disk.
\ A path names directories with / between them and matches without regard to
\ case; long file names are read. Files come from a pool and are read with the
\ standard words, whose ior is a throw code (0 for none):
\   open-file   ( addr u fam -- fileid ior )   r/o is the only access method
\   read-file   ( addr u fileid -- u2 ior )
\   read-line   ( addr u fileid -- u2 flag ior )   a CR before the LF is dropped
\   file-size   ( fileid -- ud ior )
\   close-file  ( fileid -- ior )
\   include-file ( fileid -- )  included ( addr u -- )  include ( "name" -- )
\   dir         ( "path" -- )   list a directory

-37 message: file I/O exception
-38 message: non-existent file
-276 message: too many open files
-277 message: the app disk is FAT12: make it FAT16 or FAT32
-278 message: line too long

semaphore files-lock                \ one task at a time on the app disk and its cache
: lock-files  ( i*x xt -- j*x )  files-lock locked ;

\ ---- The volume

variable app-disk   -1 app-disk !   \ the disk, or -1 if there is none
variable fat-looked                 \ the disks have been searched
variable fat-bits                   \ 12, 16 or 32
variable fat-start                  \ byte offsets on the disk: the first FAT,
variable root-start                 \ ... FAT16's root directory,
variable root-size                  \ ... its size,
variable data-start                 \ ... and cluster 2
variable cluster-bytes
variable root-cluster               \ FAT32's root directory
variable #clusters

1024 reserve constant fat-buf       \ one block of the app disk (reserved: TD-33)
variable fat-blk   -1 fat-blk !     \ which, or -1

: fat-byte  ( pos -- addr )  \ the byte at offset pos on the app disk, in the cache
  dup 10 rshift dup fat-blk @ <> if
    -1 fat-blk !  dup fat-buf swap app-disk @ blk-read  fat-blk !
  else drop then  1023 and fat-buf + ;
: le16  ( addr -- u )  dup c@ swap 1+ c@ 8 lshift or ;
: le32  ( addr -- u )  dup le16 swap 2 + le16 16 lshift or ;
: bpb16  ( offset -- u )  fat-byte le16 ;    \ fields of the boot sector
: bpb32  ( offset -- u )  fat-byte le32 ;
: power-of-2?  ( u -- flag )  dup 1- and 0= ;

: fat-volume?  ( -- flag )  \ APP-DISK holds a FAT volume labelled OS4APP: its geometry
  -1 fat-blk !
  510 bpb16 $aa55 <> if false exit then
  11 bpb16  dup 512 4097 within over power-of-2? and 0= if drop false exit then   ( bps )
  13 fat-byte c@  dup 0<> over power-of-2? and 0= if 2drop false exit then       ( bps spc )
  over * cluster-bytes !
  22 bpb16 ?dup 0= if 36 bpb32 then  over *  16 fat-byte c@ *                      ( bps fats )
  14 bpb16 2 pick *  dup fat-start !  +  dup root-start !                          ( bps root )
  17 bpb16 32 *  2 pick 1- +  2 pick /  2 pick *  dup root-size !  +  data-start !
  19 bpb16 ?dup 0= if 32 bpb32 then  *  data-start @ -  cluster-bytes @ /  #clusters !
  #clusters @ 4085 < if 12 else #clusters @ 65525 < if 16 else 32 then then  fat-bits !
  44 bpb32 root-cluster !
  fat-bits @ 32 = if 71 else 43 then fat-byte 11 s" OS4APP     " compare 0= ;

: find-app-disk  ( -- )  \ into APP-DISK, once
  fat-looked @ if exit then  true fat-looked !
  #disks 0 ?do  i app-disk !  ['] fat-volume? catch if false then  if unloop exit then  loop
  -1 app-disk ! ;
: ?volume  ( -- )  find-app-disk  app-disk @ 0< if -38 throw then  fat-bits @ 12 = if -277 throw then ;

: cluster>pos  ( cluster -- pos )  2 - cluster-bytes @ *  data-start @ + ;
: ?cluster  ( cluster -- cluster )  dup 2 #clusters @ 2 + within 0= if -37 throw then ;
: next-cluster  ( cluster -- cluster' | 0 )  \ 0 at the end of the chain
  fat-bits @ 32 = if
    4 * fat-start @ + fat-byte le32 $0fffffff and  dup $0ffffff8 u< 0= if drop 0 exit then
  else
    2* fat-start @ + fat-byte le16  dup $fff8 u< 0= if drop 0 exit then
  then ?cluster ;

\ ---- Reading a chain of clusters. A file: the link in the free list, its first
\ cluster (0 for FAT16's root directory), the cluster being read and the
\ position it starts at, the position, the size, clusters followed so far (to
\ stop at a loop in a broken chain), whether it is open, the line INCLUDE-FILE
\ is on, then the end of its name (a counted string) and a line buffer.

: f.link     ( f -- addr ) ;
: f.start    ( f -- addr )  cell+ ;
: f.cluster  ( f -- addr )  2 cells + ;
: f.cpos     ( f -- addr )  3 cells + ;
: f.pos      ( f -- addr )  4 cells + ;
: f.size     ( f -- addr )  5 cells + ;
: f.walked   ( f -- addr )  6 cells + ;
: f.open     ( f -- addr )  7 cells + ;
: f.line#    ( f -- addr )  8 cells + ;
: f.name     ( f -- addr )  9 cells + ;
: f.buf      ( f -- addr )  9 cells + 32 + ;
256 constant /line
9 cells 32 + /line + constant /file
-1 1 rshift constant unbounded      \ the size of a directory: until its chain ends

: f-init  ( cluster size f -- f )
  tuck f.size !  tuck f.start !  dup f.start @ over f.cluster !
  0 over f.cpos !  0 over f.pos !  0 over f.walked !  0 over f.line# ! ;

: advance  ( f -- flag )  \ on to the next cluster; false at the end of the chain
  1 over f.walked +!  dup f.walked @ #clusters @ u> if -37 throw then
  dup f.cluster @ next-cluster ?dup if
    over f.cluster !  cluster-bytes @ swap f.cpos +!  true
  else drop false then ;

: f-where  ( f -- pos avail )  \ where f's position is on the disk, and the bytes left in its cluster
  dup f.start @ 0= if  f.pos @  root-start @ over +  root-size @ rot - 0 max  exit  then
  dup f.pos @ over f.cpos @ - cluster-bytes @ u< 0= if  dup advance 0= if drop 0 0 exit then  then
  dup f.pos @ over f.cpos @ -  swap f.cluster @ cluster>pos over +  swap cluster-bytes @ swap - ;

: f-chunk  ( f -- addr n )  \ the next bytes of f that lie together in the cache; 0 at the end
  dup f.pos @ over f.size @ u< 0= if drop 0 0 exit then
  dup f-where ?dup 0= if 2drop 0 0 exit then             ( f pos avail )
  2 pick f.size @ 3 pick f.pos @ - min
  over 1023 and 1024 swap - min  rot drop  swap fat-byte swap ;
: f-skip  ( f n -- )  swap f.pos +! ;

: f-step  ( addr u f -- addr' u' more? )  \ copy one chunk
  >r  r@ f-chunk ?dup 0= if  drop r> drop false exit  then     ( addr u caddr n )
  2 pick min >r  2 pick r@ cmove
  r> dup r> swap f-skip  /string true ;
: f-read  ( addr u f -- u2 )  \ up to u bytes into addr; fewer at the end
  over >r >r  begin dup if r@ f-step else false then while pause repeat
  nip r> drop r> swap - ;

: lf-index  ( addr n -- i )  \ of the first line feed, or n
  tuck 0 ?do  dup i + c@ 10 = if 2drop i unloop exit then  loop drop ;
: line-step  ( addr u f -- addr' u' more? )  \ copy one chunk, up to a line feed
  >r  r@ f-chunk ?dup 0= if  drop r> drop false exit  then     ( a u ca n )
  2 pick min  2dup lf-index  tuck = >r                          ( a u ca k )
  dup >r  3 pick swap cmove  r> r>                              ( a u k no-lf )
  2dup 0= -  r> swap f-skip  >r /string r> ;
: f-line  ( addr u f -- u2 flag )
  dup f.pos @ over f.size @ u< 0= if  drop 2drop 0 false exit  then
  >r over swap  begin dup if r@ line-step else false then while repeat
  drop over -  dup if  2dup + 1- c@ 13 = if 1- then  then  nip  r> drop true ;

\ ---- Directories

create entry 32 allot               \ the directory entry being looked at
create ename 256 allot              \ its name
variable ename-len
create lfn 260 allot                \ a long name being put together
variable lfn?                       \ ... for the next entry
create lfn-offsets  1 c, 3 c, 5 c, 7 c, 9 c, 14 c, 16 c, 18 c, 20 c, 22 c, 24 c, 28 c, 30 c,
create dir-file /file allot         \ the directory being read

: +ename  ( c -- )  ename ename-len @ + c!  1 ename-len +! ;
: lfn-part  ( -- )  \ thirteen characters of a long name, from ENTRY
  entry c@ dup $40 and if  lfn 260 0 fill  true lfn? !  then
  $1f and 1-  dup 20 u< 0= if  drop false lfn? ! exit  then  13 *
  13 0 do
    lfn-offsets i + c@ entry + le16
    dup 0= over $ffff = or if drop else
      dup 127 > if drop [char] ? then  over i + lfn + c!
    then
  loop drop ;
: long-name  ( -- )  0 ename-len !  255 0 do  lfn i + c@ ?dup 0= if leave then  +ename  loop ;
: lower?  ( c flag -- c' )  if lower then ;
: short-name  ( -- )  \ NAME.EXT, lower case where ENTRY's flags say
  0 ename-len !
  entry 8 -trailing 0 ?do  dup i + c@  entry 12 + c@ 8 and lower?  +ename  loop drop
  entry 8 + 3 -trailing ?dup if
    [char] . +ename
    0 ?do  dup i + c@  entry 12 + c@ 16 and lower?  +ename  loop
  then drop ;

: next-entry  ( f -- flag )  \ the next entry of directory f into ENTRY and ENAME; false at the end
  begin
    entry 32 2 pick f-read 32 < if drop false exit then
    entry c@ 0= if drop false exit then
    entry c@ $e5 = if  false lfn? !  else
    entry 11 + c@ $0f = if  lfn-part  else
    entry 11 + c@ 8 and if  false lfn? !  else                    \ the volume label
      lfn? @ if long-name else short-name then  false lfn? !  drop true exit
    then then then
  again ;
: e-dir?     ( -- flag )  entry 11 + c@ $10 and 0<> ;
: e-cluster  ( -- u )  entry 26 + le16  fat-bits @ 32 = if  entry 20 + le16 16 lshift or  then ;
: e-size     ( -- u )  entry 28 + le32 ;

: dir-start  ( cluster -- cluster' )  dup 0= fat-bits @ 32 = and if drop root-cluster @ then ;
: open-dir   ( cluster -- f )  dir-start unbounded dir-file f-init ;

\ Paths. WALK-PATH leaves what it found in these:
variable p-cluster   variable p-size   variable p-dir?

: skip-slashes  ( addr u -- addr' u' )  begin dup while over c@ [char] / = while 1 /string repeat then ;
: split  ( addr u -- rest-addr rest-u name-addr name-u )  \ at the first /
  2dup  begin dup while over c@ [char] / <> while 1 /string repeat then
  2swap 2 pick - ;
: name-match?  ( addr u -- flag )  dup ename-len @ = if ename swap name= else 2drop false then ;
: lookup  ( addr u -- )  \ the name in directory P-CLUSTER; -38 if it is not there
  p-cluster @ open-dir >r
  begin r@ next-entry while
    2dup name-match? if
      2drop r> drop  e-cluster p-cluster !  e-size p-size !  e-dir? p-dir? !  exit
    then
  repeat  2drop r> drop  -38 throw ;
: walk-path  ( addr u -- )  \ the file or directory at the path
  ?volume  0 p-cluster !  unbounded p-size !  true p-dir? !
  begin skip-slashes dup while
    p-dir? @ 0= if -38 throw then
    split lookup
  repeat 2drop ;

\ ---- Open files, from a pool

variable free-files
variable #files                     \ made so far
16 constant max-files
0 constant r/o

: new-file  ( -- f )
  free-files @ ?dup if  dup f.link @ free-files !  exit  then
  #files @ max-files < 0= if -276 throw then
  /file reserve  1 #files +! ;
: ?open  ( f -- f )  dup f.open @ 0= if -37 throw then ;

: (open-file)  ( addr u -- f )
  2dup walk-path  p-dir? @ if -38 throw then
  new-file >r  p-cluster @ p-size @ r@ f-init drop  true r@ f.open !
  dup 31 - 0 max /string  dup r@ f.name c!  r@ f.name 1+ swap cmove  r> ;
: (close-file)  ( f -- )  ?open  false over f.open !  free-files @ over f.link !  free-files ! ;
: (read-file)  ( addr u f -- u2 )  ?open f-read ;
: (read-line)  ( addr u f -- u2 flag )  ?open f-line ;

: open-file  ( addr u fam -- fileid ior )
  drop  ['] (open-file) ['] lock-files catch ?dup if  >r drop 2drop 0 r>  else 0 then ;
: close-file  ( fileid -- ior )
  ['] (close-file) ['] lock-files catch ?dup if nip nip else 0 then ;
: read-file  ( addr u fileid -- u2 ior )
  ['] (read-file) ['] lock-files catch ?dup if  >r 2drop 2drop 0 r>  else 0 then ;
: read-line  ( addr u fileid -- u2 flag ior )
  ['] (read-line) ['] lock-files catch ?dup if  >r 2drop 2drop 0 false r>  else 0 then ;
: file-size  ( fileid -- ud ior )  dup f.open @ if f.size @ 0 0 else drop 0 0 -37 then ;

\ ---- Loading source from files, a line at a time

\ The file stays on the return stack: a definition open across lines keeps its
\ control-flow values on the data stack.
: include-lines  ( f -- )
  >r  begin  r@ f.buf /line r@ read-line throw  while
    dup /line = if -278 throw then
    #tib !  r@ f.buf 'tib !  0 >in !  1 r@ f.line# +!
    'interpret @ execute  pause
  repeat  drop r> drop ;
: note-error  ( f -- )  \ where the error was, unless an inner file or block said already
  error-line @ error-blk @ or if drop exit then
  dup f.line# @ error-line !  f.name dup c@ 1+ error-file swap cmove ;
: include-file  ( i*x fileid -- j*x )  \ and close it
  blk @ >r  'tib @ >r  #tib @ >r  >in @ >r  0 blk !
  dup >r ['] include-lines catch ?dup if  nip r@ note-error  else 0 then
  r> close-file drop
  r> >in !  r> #tib !  r> 'tib !  r> blk !  throw ;
: included  ( i*x addr u -- j*x )  r/o open-file throw include-file ;
: include   ( i*x "name" -- j*x )  parse-name included ;

\ ---- Looking at the app disk

: .entry  ( -- )
  ename ename-len @ type  e-dir? if [char] / emit else space e-size (.) type then cr ;
: (dir)  ( addr u -- )
  walk-path  p-dir? @ 0= if -38 throw then
  p-cluster @ open-dir  begin dup next-entry while  entry c@ [char] . <> if .entry then  repeat drop ;
: dir  ( "path" -- )  parse-name ['] (dir) lock-files ;
