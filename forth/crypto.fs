\ crypto.fs: SHA-256 (FIPS 180-4), HMAC-SHA-256 (RFC 2104) and PBKDF2 (RFC
\ 8018), for password hashes: a password is stored as a random salt, an
\ iteration count and PBKDF2-HMAC-SHA-256 of the two, so checking a guess costs
\ the attacker as much as it costs us. SHA-256 works on 32-bit words; cells are
\ 64 bits, so results are masked. The hash state is shared: SHA256 never
\ pauses, and the words that do (PBKDF2, between iterations) hold HASH-LOCK.

: m32    ( x -- x' )  $ffffffff and ;
: ror32  ( x n -- x' )  2dup rshift -rot 32 swap - lshift or m32 ;   \ x is 32 bits
: be@    ( addr -- x )  0 swap 4 0 do  swap 8 lshift over i + c@ or swap  loop drop ;
: be!    ( x addr -- )  4 0 do  over 24 i 8 * - rshift $ff and  over i + c!  loop 2drop ;

create k256
  $428a2f98 , $71374491 , $b5c0fbcf , $e9b5dba5 , $3956c25b , $59f111f1 , $923f82a4 , $ab1c5ed5 ,
  $d807aa98 , $12835b01 , $243185be , $550c7dc3 , $72be5d74 , $80deb1fe , $9bdc06a7 , $c19bf174 ,
  $e49b69c1 , $efbe4786 , $0fc19dc6 , $240ca1cc , $2de92c6f , $4a7484aa , $5cb0a9dc , $76f988da ,
  $983e5152 , $a831c66d , $b00327c8 , $bf597fc7 , $c6e00bf3 , $d5a79147 , $06ca6351 , $14292967 ,
  $27b70a85 , $2e1b2138 , $4d2c6dfc , $53380d13 , $650a7354 , $766a0abb , $81c2c92e , $92722c85 ,
  $a2bfe8a1 , $a81a664b , $c24b8b70 , $c76c51a3 , $d192e819 , $d6990624 , $f40e3585 , $106aa070 ,
  $19a4c116 , $1e376c08 , $2748774c , $34b0bcb5 , $391c0cb3 , $4ed8aa4a , $5b9cca4f , $682e6ff3 ,
  $748f82ee , $78a5636f , $84c87814 , $8cc70208 , $90befffa , $a4506ceb , $bef9a3f7 , $c67178f2 ,
create h256-init
  $6a09e667 , $bb67ae85 , $3c6ef372 , $a54ff53a , $510e527f , $9b05688c , $1f83d9ab , $5be0cd19 ,

create sha-h  8 cells allot     \ the hash so far
create sha-v  8 cells allot     \ the working variables a to h, rotating: see V
create sha-w  64 cells allot    \ the message schedule
create sha-buf  64 allot        \ the block being filled
variable sha-count              \ bytes hashed so far
variable sha-r                  \ rounds done in this block

: cells-move  ( src dst n -- )  cells move ;
: w@  ( i -- x )  cells sha-w + @ ;
\ Each round shifts a to h along by one. Rather than move them, the index
\ turns: working variable i is in cell i - rounds (mod 8).
: v   ( i -- addr )  sha-r @ - 7 and cells sha-v + ;
: v@  ( i -- x )  v @ ;

: schedule  ( addr -- )  \ the 64 words for one 64-byte block
  16 0 do  dup i 4 * + be@  i cells sha-w + !  loop drop
  64 16 do
    i 2 - w@  dup 17 ror32  over 19 ror32 xor  swap 10 rshift xor
    i 15 - w@  dup 7 ror32  over 18 ror32 xor  swap 3 rshift xor  +
    i 16 - w@ +  i 7 - w@ +  m32  i cells sha-w + !
  loop ;

: big-sigma1  ( -- x )  4 v@  dup 6 ror32  over 11 ror32 xor  swap 25 ror32 xor ;
: big-sigma0  ( -- x )  0 v@  dup 2 ror32  over 13 ror32 xor  swap 22 ror32 xor ;
: sha-choose      ( -- x )  4 v@ 5 v@ and  4 v@ $ffffffff xor 6 v@ and  xor ;
: sha-majority    ( -- x )  0 v@ 1 v@ and  0 v@ 2 v@ and xor  1 v@ 2 v@ and xor ;

: sha-round  ( i -- )
  dup cells k256 + @  swap w@ +  7 v@ +  big-sigma1 +  sha-choose +  m32     ( t1 )
  big-sigma0 sha-majority + m32                                             ( t1 t2 )
  over 3 v@ + m32 3 v !                             \ d + t1, the next round's e
  + m32 7 v !                                       \ t1 + t2, the next round's a
  1 sha-r +! ;

\ Fold one 64-byte block into the hash. The kernel's SHA256-BLOCK does this;
\ COMPRESS-REF is its definition, which tests/reference checks it against.
: compress-ref  ( addr -- )
  schedule
  sha-h sha-v 8 cells-move  0 sha-r !
  64 0 do i sha-round loop                          \ 64 rounds: the index is back at 0
  8 0 do  i cells sha-h +  dup @ i cells sha-v + @ + m32  swap !  loop ;
: compress  ( addr -- )  sha-h sha-w k256 sha256-block ;

: sha-init  ( -- )  h256-init sha-h 8 cells-move  0 sha-count ! ;
: sha-byte  ( c -- )
  sha-count @ 63 and sha-buf + c!  1 sha-count +!
  sha-count @ 63 and 0= if sha-buf compress then ;
: sha-update  ( addr len -- )  over + swap ?do  i c@ sha-byte  loop ;
: sha-final  ( out -- )  \ pad, and store the 32-byte hash at out
  sha-count @ 8 *
  $80 sha-byte  begin sha-count @ 63 and 56 <> while 0 sha-byte repeat
  8 0 do  dup 56 i 8 * - rshift $ff and sha-byte  loop drop
  sha-h swap sha256-out ;
: sha256  ( addr len out -- )  >r sha-init sha-update r> sha-final ;

\ ---- HMAC. The states after the key's inner and outer pads are kept, so each
\ HMAC of a short message costs two compressions, not four.

create hmac-key  64 allot
create inner-h  8 cells allot
create outer-h  8 cells allot
create hmac-mid  32 allot

: keyed  ( pad state -- )  \ hash the key xor pad, and keep the state
  sha-init  swap 64 0 do  hmac-key i + c@ over xor sha-byte  loop drop
  sha-h swap 8 cells-move ;
: hmac-key!  ( addr len -- )
  hmac-key 64 0 fill
  dup 64 > if  hmac-key sha256  else  hmac-key swap move  then
  $36 inner-h keyed  $5c outer-h keyed ;
: resume  ( state -- )  sha-h 8 cells-move  64 sha-count ! ;
: hmac  ( addr len out -- )  \ under the key from HMAC-KEY!
  >r  inner-h resume sha-update  hmac-mid sha-final
  outer-h resume  hmac-mid 32 sha-update  r> sha-final ;

semaphore hash-lock
: (hmac-sha256)  ( addr len key klen out -- )  >r hmac-key! r> hmac ;
: hmac-sha256  ( addr len key klen out -- )  ['] (hmac-sha256) hash-lock locked ;

\ ---- PBKDF2-HMAC-SHA-256, one 32-byte block. Each iteration after the first
\ is the HMAC of the last one's 32 bytes: from each saved key state, a single
\ block of message and padding. Those two blocks are laid out once, so an
\ iteration is two compressions. It pauses after each iteration, so a slow
\ hash does not hold up other tasks.

create u-block  32 allot
create t-block  32 allot
create block-1  0 c, 0 c, 0 c, 1 c,
create inner-blk  64 allot
create outer-blk  64 allot
: pad-32  ( blk -- )  \ padding for 32 bytes after a 64-byte block: 768 bits
  dup 64 0 fill  $80 over 32 + c!  3 swap 62 + c! ;
: hmac32  ( -- )  \ the HMAC of the 32 bytes at INNER-BLK, written back there
  inner-h sha-h 8 cells-move  inner-blk compress  sha-h outer-blk sha256-out
  outer-h sha-h 8 cells-move  outer-blk compress  sha-h inner-blk sha256-out ;
: xor-32  ( src dst -- )  4 0 do  over i cells + @  over i cells + dup @ rot xor swap !  loop 2drop ;
: (pbkdf2)  ( pass plen salt slen n out -- )
  >r >r  2swap hmac-key!
  inner-h resume  sha-update  block-1 4 sha-update  hmac-mid sha-final
  outer-h resume  hmac-mid 32 sha-update  u-block sha-final
  u-block t-block 32 move
  inner-blk pad-32  outer-blk pad-32  u-block inner-blk 32 move
  r> 1 ?do  hmac32  inner-blk t-block xor-32  pause  loop
  t-block r> 32 move ;
: pbkdf2  ( pass plen salt slen n out -- )  ['] (pbkdf2) hash-lock locked ;

\ ---- Password hashes: the iteration count, a 16-byte salt and the 32-byte
\ hash. New hashes take as many iterations as this machine runs in HASH-MS,
\ measured the first time one is made, but never fewer than MIN-ITERATIONS.
\ The count is stored with each hash, so hashes stay valid on other machines.

0
1 cells field pw.iterations
16 field pw.salt
32 field pw.hash
constant /password
variable hash-iterations        \ for new hashes; 0 until measured
250 constant hash-ms
1000 constant min-iterations
create pw-check 32 allot

: calibrate  ( -- n )  \ iterations that take about HASH-MS here
  counter  pw-check 8 pw-check 8 200 pw-check pbkdf2  counter swap - 1 max
  >r  200 hash-ms * counter-hz 1000 / *  r> /  min-iterations max ;
: iterations  ( -- n )
  hash-iterations @ ?dup 0= if  calibrate dup hash-iterations !  then ;
: hash-password  ( addr len pw -- )  \ a new salt, and the hash of the password
  >r  iterations r@ pw.iterations !
  random r@ pw.salt !  random r@ pw.salt cell+ !
  r@ pw.salt 16 r@ pw.iterations @ r> pw.hash pbkdf2 ;
: (password?)  ( addr len pw -- flag )
  >r  r@ pw.salt 16 r@ pw.iterations @ pw-check (pbkdf2)
  pw-check 32 r> pw.hash 32 compare 0= ;
: password?  ( addr len pw -- flag )  \ the password matches the hash
  ['] (password?) hash-lock locked ;
