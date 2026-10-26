\ blocks.fs: Forth blocks on the data disk, through the block HAL (hal/).
\ 1 KiB blocks are cached in buffers. UPDATE marks the current buffer changed,
\ SAVE-BUFFERS writes changes back, and SYNC also flushes the device: only
\ then is a change durable.
\ Block 0 holds the disk header written by tools/blocks.py: magic, format
\ version, volume ID and size. A disk without a valid header is read-only, and
\ block 0 itself is never written.

-33 message: block read error
-34 message: block write error
-35 message: invalid block number
-257 message: no data disk
-258 message: the data disk has no valid header, so it is read-only
-259 message: block 0 holds the disk header and cannot be written
-260 message: all block buffers are in use

1024 constant b/buf
semaphore blocks-lock       \ one task at a time in the buffers and on the disk

\ ---- The disk header

1 constant disk-version
create header b/buf allot
variable mounted        \ the header has been read
variable disk-ok        \ ... and is valid
variable #blocks        \ blocks usable on this disk
variable volume-id

: mount  ( -- )  \ read the header, once
  mounted @ if exit then
  blk-count dup 0= if -257 throw then  #blocks !
  header 0 blk-read
  header 8 s" OS40DISK" compare 0=  header 8 + @ disk-version = and  disk-ok !
  disk-ok @ if  header 16 + @ volume-id !  header 24 + @ #blocks @ min #blocks !  then
  true mounted ! ;

: ?block     ( u -- u )  mount  dup #blocks @ u< 0= if -35 throw then ;
: ?writable  ( u -- u )  disk-ok @ 0= if -258 throw then  dup 0= if -259 throw then ;

: .disk  ( -- )  \ describe the data disk
  ['] mount blocks-lock locked
  disk-ok @ if ." volume " volume-id @ (.) type ." , " else ." no valid header, " then
  #blocks @ (.) type ."  blocks" ;

\ ---- Buffers. Each holds one block; LOAD pins the buffer it is reading from.

\ Tasks share the buffers: each public word below holds BLOCKS-LOCK, so a task
\ that pauses mid-request (waiting for the disk) cannot have its buffer taken.
\ An address from BLOCK stays valid only until the task next pauses, unless
\ its buffer is pinned (as LOAD does).

8 constant #buffers
create buffers  #buffers b/buf * allot
create buf-blocks  #buffers cells allot   \ the block in each buffer, or -1
create buf-dirty   #buffers cells allot   \ true once UPDATEd
create buf-pins    #buffers cells allot   \ LOADs reading from it
user last-buf                             \ the buffer this task's BLOCK or BUFFER returned last
variable next-buf                         \ where the search for a free one starts

: buf    ( i -- addr )  b/buf * buffers + ;
: 'blk   ( i -- addr )  cells buf-blocks + ;
: 'dirty ( i -- addr )  cells buf-dirty + ;
: 'pins  ( i -- addr )  cells buf-pins + ;
: pin    ( i -- )  1 swap 'pins +! ;
: unpin  ( i -- )  -1 swap 'pins +! ;

: (empty-buffers)  ( -- )
  #buffers 0 do  -1 i 'blk !  0 i 'dirty !  0 i 'pins !  loop ;
(empty-buffers)

: buf-of  ( u -- i | -1 )  \ the buffer holding block u
  #buffers 0 do  dup i 'blk @ = if drop i unloop exit then  loop drop -1 ;

: write-buf  ( i -- )  \ write buffer i back if it was updated
  dup 'dirty @ if
    dup buf over 'blk @ ?writable blk-write  0 swap 'dirty !
  else drop then ;

: victim  ( -- i )  \ the next unpinned buffer, round robin, written back first
  #buffers 0 do
    next-buf @ 1+ #buffers mod  dup next-buf !
    dup 'pins @ 0= if  dup write-buf unloop exit  then drop
  loop -260 throw ;

: (buffer)  ( u -- addr )
  ?block dup buf-of dup 0< if
    drop victim  tuck 'blk !  0 over 'dirty !
  else nip then
  dup last-buf !  buf ;

: (block)  ( u -- addr )
  dup buf-of 0< if
    dup dup (buffer) swap  ['] blk-read catch ?dup if
      nip nip  -1 last-buf @ 'blk !  throw
    then
  then (buffer) ;

: (update)        ( -- )  last-buf @ dup 'blk @ ?writable drop  true swap 'dirty ! ;
: (save-buffers)  ( -- )  #buffers 0 do i write-buf loop ;

: buffer  ( u -- addr )  \ a buffer for block u, without reading it from disk
  ['] (buffer) blocks-lock locked ;
: block   ( u -- addr )  \ block u, read from disk unless already buffered
  ['] (block) blocks-lock locked ;
: update         ( -- )  ['] (update) blocks-lock locked ;   \ the last buffer this task got
: save-buffers   ( -- )  ['] (save-buffers) blocks-lock locked ;
: empty-buffers  ( -- )  ['] (empty-buffers) blocks-lock locked ;  \ discarding changes
: (flush)  ( -- )  (save-buffers) (empty-buffers) ;
: flush          ( -- )  ['] (flush) blocks-lock locked ;
: (sync)   ( -- )  (save-buffers) blk-flush ;
: sync           ( -- )  ['] (sync) blocks-lock locked ;  \ durable once this returns

\ ---- Loading source from blocks. A block is 16 lines of 64 characters.

variable error-blk      \ where an error in a LOADed block happened, for .ERROR
variable error-in
variable 'interpret     \ xt of INTERPRET, set by interpreter.fs

: load  ( i*x u -- j*x )
  blk @ >r  'tib @ >r  #tib @ >r  >in @ >r
  dup block 'tib !  blk !  b/buf #tib !  0 >in !
  last-buf @ dup >r pin
  'interpret @ catch
  ?dup if  error-blk @ 0= if  blk @ error-blk !  >in @ error-in !  then  else 0 then
  r> unpin  r> >in !  r> #tib !  r> 'tib !  r> blk !
  throw ;
: thru  ( from to -- )  1+ swap ?do i load loop ;

: \  ( -- )  \ comment to the end of the line: of 64 characters, in a block
  blk @ if  >in @ 62 + -64 and  else  #tib @  then  >in ! ; immediate

\ ---- Looking at and editing blocks

user scr                \ the screen LIST, WIPE and >LINE work on, per task

: .line  ( addr u -- )  \ a space, then the text, if the line is not blank
  -trailing ?dup if
    space 0 ?do  dup c@ dup bl < if drop bl then emit 1+  loop
  then drop ;
: list   ( u -- )
  dup scr !  ." Screen " dup (.) type cr
  16 0 do  i 2 .r  dup block i 64 * + 64 .line cr  loop drop ;
: index  ( from to -- )  \ the first line of each block
  1+ swap ?do  i 4 .r  i block 64 .line cr  loop ;
: line   ( n -- addr )  dup 16 u< 0= if -24 throw then  64 *  scr @ block + ;
: wipe   ( u -- )  \ blank block u and make it the current screen
  dup scr !  buffer b/buf bl fill update ;
: >line  ( n "text" -- )  \ replace line n of the current screen with the rest of this line
  line  0 parse  rot dup 64 bl fill  swap 64 min cmove  update ;
