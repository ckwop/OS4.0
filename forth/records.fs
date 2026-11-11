\ records.fs: small binary records on the data disk that survive a crash. A
\ record has two blocks, n and n+1, written in turn. Each copy holds a checksum,
\ a sequence number, the data's length and the data, so a write torn by a crash
\ spoils only the copy being written; reading takes the newest copy whose
\ checksum holds. Every write is synced before RECORD! returns. Records hold up
\ to 1000 bytes of binary data, never Forth source.

-274 message: record too large

0
1 cells field r.check           \ SipHash of everything after it, up to the data's end
1 cells field r.seq             \ 1 for the first write; 0 means never written
1 cells field r.len
0 field r.data
constant /record-header
b/buf /record-header - constant /record

$4f53345245434f52 constant record-k0   \ a fixed key: this is a checksum, not a secret
$636865636b73756d constant record-k1

semaphore records-lock

: record-sum  ( buf -- u )  dup r.seq  swap r.len @ 16 +  record-k0 record-k1 siphash ;
: copy-seq  ( blk -- seq | 0 )  \ the sequence number of a copy, 0 if it is not valid
  block  dup r.len @ /record u> if drop 0 exit then
  dup record-sum over r.check @ = if r.seq @ else drop 0 then ;

\ Sequence numbers are serial numbers (RFC 1982): copy 1 is the newer when
\ s1 - s0, taken as signed, is positive, so the count may wrap. 0 means never
\ written, older than anything, and the number after the newest skips it. Reading
\ and writing must agree on which copy is the newer (defect 40).
: newer?    ( s0 s1 -- flag )  \ copy 1 is the newer, or the only valid one
  over 0= if nip 0<> exit then  dup 0= if 2drop false exit then  swap - 0> ;
: next-seq  ( s -- s' )  1+ dup 0= - ;

: (record@)  ( addr max n -- len | -1 )
  dup copy-seq  over 1+ copy-seq                   ( addr max n s0 s1 )
  2dup or 0= if  2drop 2drop drop -1 exit  then
  newer? if 1+ then                                 \ the newer copy
  block  dup r.len @ /record umin rot umin >r       ( addr buf )   \ re-read: bound it again
  r.data swap r@ move  r> ;

\ Fill a buffer for block n and mark it changed, holding the buffers throughout
\ so that no other task can reuse it in between. A block that cannot be written
\ is refused before its buffer changes: a buffer filled and then refused would
\ hold a copy that never reaches the disk, and RECORD@ would read it (defect 39).
: fill-copy  ( addr len seq n -- )
  ?block ?writable  (buffer)  dup b/buf 0 fill      ( addr len seq buf )
  tuck r.seq !  2dup r.len !
  >r  r@ r.data swap move
  r@ record-sum r> r.check !
  (update) ;
\ The older copy is overwritten only while the newer one is durable: after a
\ failed sync (a write or the flush), the newer one might be only in a buffer.
: (record!)  ( addr len n -- )
  over /record u> if -274 throw then
  unsynced @ if sync then
  dup copy-seq  over 1+ copy-seq                   ( addr len n s0 s1 )
  2dup newer? if  nip next-seq swap  else  drop next-seq swap 1+  then   \ the next number, over the older copy
  ['] fill-copy blocks-lock locked
  sync ;

: record@  ( addr max n -- len | -1 )  \ the record in blocks n and n+1, -1 if there is none
  ['] (record@) records-lock locked ;
: record!  ( addr len n -- )  \ write it, durably, to blocks n and n+1
  ['] (record!) records-lock locked ;
