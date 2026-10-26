\ core.fs: the language itself, built on the kernel's primitives.
\ The kernel (arch/aarch64/kernel.s) provides the primitives, the bootstrap
\ interpreter and the compiler basics: : ; [ ] header cf, immediate parse ...
\ It loads the boot files listed in kernel.s in order, starting with this one.
\ Keep these files portable: no knowledge of the CPU or platform.

\ ---- Stack

: rot    ( a b c -- b c a )  >r swap r> swap ;
: -rot   ( a b c -- c a b )  rot rot ;
: nip    ( a b -- b )  swap drop ;
: tuck   ( a b -- b a b )  swap over ;
: 2dup   ( a b -- a b a b )  over over ;
: 2drop  ( a b -- )  drop drop ;
: 2swap  ( a b c d -- c d a b )  rot >r rot r> ;
: 2over  ( a b c d -- a b c d a b )  3 pick 3 pick ;

\ ---- Arithmetic

: 1+      ( n -- n+1 )  1 + ;
: 1-      ( n -- n-1 )  1 - ;
: negate  ( n -- -n )  0 swap - ;
: /       ( n1 n2 -- quot )  /mod nip ;
: mod     ( n1 n2 -- rem )  /mod drop ;
: 2*      ( n -- n*2 )  1 lshift ;
: cells   ( n -- n*8 )  3 lshift ;
: cell+   ( addr -- addr+8 )  8 + ;
: chars   ( n -- n )  ;
: char+   ( addr -- addr+1 )  1+ ;
: +!      ( n addr -- )  dup @ rot + swap ! ;

\ ---- Comparison

: 0<>  ( x -- flag )  0= 0= ;
: <>   ( a b -- flag )  = 0= ;
: >    ( n1 n2 -- flag )  swap < ;
: u>   ( u1 u2 -- flag )  swap u< ;
: 0>   ( n -- flag )  0 swap < ;

\ ---- Dictionary and compiling

: here     ( -- addr )  dp @ ;
: allot    ( n -- )  dp +! ;
: c,       ( c -- )  here c! 1 allot ;
: aligned  ( addr -- addr' )  7 + -8 and ;
: align    ( -- )  here aligned dp ! ;
\ Header flags byte: bit 7 immediate, bit 6 hidden, bit 5 compile-only, bits 0-4 length.
: compile-only  ( -- )  latest @ cell+ dup c@ 32 or swap c! ;  \ refused outside definitions
: literal  ( x -- )  lit lit , , ; immediate compile-only   \ compiles: lit x
: '        ( "name" -- xt )  parse-find drop ;
: [']      ( "name" -- )  ' [ ' literal , ] ; immediate compile-only
: name>string  ( nt -- addr len )  cell+ dup 1+ swap c@ 31 and ;
: name>xt  ( nt -- xt )  name>string + aligned ;
: recurse  ( -- )  latest @ name>xt , ; immediate compile-only

\ ---- Control flow. Branches hold absolute target addresses.

: if    ( C: -- orig )  ['] 0branch , here 0 , ; immediate compile-only
: then  ( C: orig -- )  here swap ! ; immediate compile-only
: else  ( C: orig1 -- orig2 )  ['] branch , here 0 ,  swap here swap ! ; immediate compile-only

: postpone  ( "name" -- )
  parse-find 0< if  ['] lit , ,  ['] , ,  else  ,  then ; immediate compile-only

: begin   ( C: -- dest )  here ; immediate compile-only
: until   ( C: dest -- )  postpone 0branch , ; immediate compile-only
: again   ( C: dest -- )  postpone branch , ; immediate compile-only
: while   ( C: dest -- orig dest )  postpone if swap ; immediate compile-only
: repeat  ( C: orig dest -- )  postpone again postpone then ; immediate compile-only

: ?dup    ( x -- 0 | x x )  dup if dup then ;
: abs     ( n -- u )  dup 0< if negate then ;
: min     ( n1 n2 -- n )  2dup > if swap then drop ;
: max     ( n1 n2 -- n )  2dup < if swap then drop ;
: within  ( n lo hi -- flag )  over - >r - r> u< ;

\ ---- Defining words

: create    ( "name" -- )  parse-name header dovar cf, ;
: variable  ( "name" -- )  create 0 , ;
: constant  ( x "name" -- )  parse-name header docon cf, , ;
: does>     ( -- )  postpone (does>) does-cf, ; immediate compile-only
: >body     ( xt -- addr )  cell+ ;

-1 constant true
0 constant false
32 constant bl

\ ---- Exceptions. CATCH runs an xt and returns 0, or the code passed to THROW
\ by it or anything it calls, with the data stack restored to its depth at
\ CATCH. Each CATCH frame on the return stack holds the saved data stack
\ pointer and the enclosing frame; HANDLER (per task) points to the innermost.
\ Codes: -1 ABORT, -2 ABORT", -4 stack underflow, -10 division by zero,
\ -11 result out of range, -13 undefined word, -14 compile-only word,
\ -16 missing name, -19 name too long, -256 CPU exception (already reported).

: catch  ( i*x xt -- j*x 0 | i*x n )
  sp@ >r  handler @ >r  rp@ handler !
  execute
  r> handler !  r> drop  0 ;
: throw  ( k*x n -- k*x | i*x n )
  ?dup if
    handler @ 0= if abort then   \ nothing to catch it: the kernel's ABORT
    handler @ rp!  r> handler !  r> swap >r  sp! drop  r>
  then ;
' throw 'throw !                 \ kernel-detected errors throw from now on
: abort  ( i*x -- )  -1 throw ;

\ The dictionary is a fixed size: growing it past the end throws -8.
\ (The kernel's , and HEADER check for themselves.)
\ Deadlines, for timeouts: a counter value some milliseconds from now.
: deadline  ( ms -- u )  counter-hz 1000 / *  counter + ;
: expired?  ( u -- flag )  counter - 0< ;

: unused  ( -- u )  dict-end here - ;
: allot   ( n -- )  dup unused > if -8 throw then  allot ;
: c,      ( c -- )  here c! 1 allot ;

\ ---- Counted loops. ?DO and LEAVE add forward branches to a chain that
\ LOOP and +LOOP resolve; DO saves the enclosing loop's chain.

variable leaves
: >leaves  ( addr -- )  leaves @ over !  leaves ! ;
: resolve-leaves  ( -- )
  leaves @ begin ?dup while  dup @ swap  here swap !  repeat ;

: do     ( C: -- leaves dest )  postpone (do)  leaves @ 0 leaves !  here ; immediate compile-only
: ?do    ( C: -- leaves dest )
  postpone (?do)  leaves @ 0 leaves !  here 0 , >leaves  here ; immediate compile-only
: leave  ( -- )  postpone unloop postpone branch  here 0 , >leaves ; immediate compile-only
: loop   ( C: leaves dest -- )  postpone (loop) ,  resolve-leaves leaves ! ; immediate compile-only
: +loop  ( C: leaves dest -- )  postpone (+loop) ,  resolve-leaves leaves ! ; immediate compile-only

\ ---- Memory

: cmove   ( src dst u -- )  0 ?do  over i + c@  over i + c!  loop 2drop ;
: cmove>  ( src dst u -- )
  begin dup while  1- >r  over r@ + c@  over r@ + c!  r>  repeat drop 2drop ;
: move    ( src dst u -- )  >r 2dup u< if r> cmove> else r> cmove then ;
: fill    ( addr u c -- )  swap 0 ?do  2dup swap i + c!  loop 2drop ;
: count   ( addr -- addr+1 c )  dup 1+ swap c@ ;
: /string ( addr u n -- addr+n u-n )  tuck - >r + r> ;
: 2!      ( x1 x2 addr -- )  swap over ! cell+ ! ;
: 2@      ( addr -- x1 x2 )  dup cell+ @ swap @ ;
: compare ( addr1 u1 addr2 u2 -- n )  \ -1, 0 or 1: byte by byte, then by length
  rot 2dup >r >r min
  0 ?do
    over i + c@  over i + c@  - ?dup if
      0< if -1 else 1 then  nip nip  unloop r> r> 2drop exit
    then
  loop 2drop
  r> r> 2dup = if 2drop 0 exit then  < if 1 else -1 then ;

