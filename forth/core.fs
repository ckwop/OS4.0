\ core.fs: the Forth half of the system, interpreted by the kernel at start-up.
\ The kernel (arch/aarch64/kernel.s) provides the primitives, the outer
\ interpreter and the compiler basics: : ; [ ] header cf, immediate parse ...
\ Keep this file portable: no knowledge of the CPU or platform.

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
: literal  ( x -- )  lit lit , , ; immediate   \ compiles: lit x
: '        ( "name" -- xt )  parse-find drop ;
: [']      ( "name" -- )  ' [ ' literal , ] ; immediate
: name>string  ( nt -- addr len )  cell+ dup 1+ swap c@ 31 and ;
: name>xt  ( nt -- xt )  name>string + aligned ;
: recurse  ( -- )  latest @ name>xt , ; immediate

\ ---- Control flow. Branches hold absolute target addresses.

: if    ( C: -- orig )  ['] 0branch , here 0 , ; immediate
: then  ( C: orig -- )  here swap ! ; immediate
: else  ( C: orig1 -- orig2 )  ['] branch , here 0 ,  swap here swap ! ; immediate

: postpone  ( "name" -- )
  parse-find 0< if  ['] lit , ,  ['] , ,  else  ,  then ; immediate

: begin   ( C: -- dest )  here ; immediate
: until   ( C: dest -- )  postpone 0branch , ; immediate
: again   ( C: dest -- )  postpone branch , ; immediate
: while   ( C: dest -- orig dest )  postpone if swap ; immediate
: repeat  ( C: orig dest -- )  postpone again postpone then ; immediate

: ?dup    ( x -- 0 | x x )  dup if dup then ;
: abs     ( n -- u )  dup 0< if negate then ;
: min     ( n1 n2 -- n )  2dup > if swap then drop ;
: max     ( n1 n2 -- n )  2dup < if swap then drop ;
: within  ( n lo hi -- flag )  over - >r - r> u< ;

\ ---- Defining words

: create    ( "name" -- )  parse-name header dovar cf, ;
: variable  ( "name" -- )  create 0 , ;
: constant  ( x "name" -- )  parse-name header docon cf, , ;
: does>     ( -- )  postpone (does>) does-cf, ; immediate
: >body     ( xt -- addr )  cell+ ;

-1 constant true
0 constant false
32 constant bl

\ ---- Counted loops. ?DO and LEAVE add forward branches to a chain that
\ LOOP and +LOOP resolve; DO saves the enclosing loop's chain.

variable leaves
: >leaves  ( addr -- )  leaves @ over !  leaves ! ;
: resolve-leaves  ( -- )
  leaves @ begin ?dup while  dup @ swap  here swap !  repeat ;

: do     ( C: -- leaves dest )  postpone (do)  leaves @ 0 leaves !  here ; immediate
: ?do    ( C: -- leaves dest )
  postpone (?do)  leaves @ 0 leaves !  here 0 , >leaves  here ; immediate
: leave  ( -- )  postpone unloop postpone branch  here 0 , >leaves ; immediate
: loop   ( C: leaves dest -- )  postpone (loop) ,  resolve-leaves leaves ! ; immediate
: +loop  ( C: leaves dest -- )  postpone (+loop) ,  resolve-leaves leaves ! ; immediate

\ ---- Memory

: cmove   ( src dst u -- )  0 ?do  over i + c@  over i + c!  loop 2drop ;
: cmove>  ( src dst u -- )
  begin dup while  1- >r  over r@ + c@  over r@ + c!  r>  repeat drop 2drop ;
: move    ( src dst u -- )  >r 2dup u< if r> cmove> else r> cmove then ;
: fill    ( addr u c -- )  swap 0 ?do  2dup swap i + c!  loop 2drop ;
: count   ( addr -- addr+1 c )  dup 1+ swap c@ ;

\ ---- Terminal output

: cr      ( -- )  10 emit ;
: space   ( -- )  bl emit ;
: spaces  ( n -- )  begin dup 0> while space 1- repeat drop ;
: type    ( addr u -- )  0 ?do  dup c@ emit 1+  loop drop ;

\ ---- Number output. Pictured output builds digits backwards from the end of numbuf.

: decimal  ( -- )  10 base ! ;
: hex      ( -- )  16 base ! ;

create numbuf 128 allot
variable hld
: <#     ( -- )  numbuf 128 + hld ! ;
: hold   ( c -- )  -1 hld +!  hld @ c! ;
: digit  ( u -- c )  dup 9 > if 7 + then 48 + ;
: #      ( ud -- ud' )  0 base @ um/mod >r  base @ um/mod  r> rot digit hold ;
: #s     ( ud -- 0 0 )  begin # 2dup or 0= until ;
: #>     ( ud -- addr u )  2drop  hld @  numbuf 128 + over - ;
: sign   ( n -- )  0< if 45 hold then ;
: u.     ( u -- )  0 <# #s #> type space ;
: .      ( n -- )  dup >r abs 0 <# #s r> sign #> type space ;
: .s     ( -- )
  60 emit depth 0 <# #s #> type 62 emit space
  depth 0 ?do  depth i - 1- pick .  loop ;

\ ---- Strings. A compiled string is a length cell, then the characters, aligned.

: (s")  ( -- addr u )  r> dup cell+ swap @  2dup + aligned >r ;
: s,    ( addr u -- )  dup , here swap dup allot cmove align ;
create sbuf 256 allot
: s"    ( "ccc<quote>" -- addr u )
  34 parse  state @ if  postpone (s") s,  else  dup >r sbuf swap cmove sbuf r>  then ; immediate
: ."      ( "ccc<quote>" -- )
  state @ if  postpone s" postpone type  else  34 parse type  then ; immediate
: .(      ( "ccc<paren>" -- )  41 parse type ; immediate
: abort"  ( flag "ccc<quote>" -- )
  postpone if postpone ." postpone cr postpone abort postpone then ; immediate
: char    ( "name" -- c )  parse-name drop c@ ;
: [char]  ( "name" -- )  char postpone literal ; immediate

\ ---- Tools

: source  ( -- addr u )  'tib @ #tib @ ;
: words   ( -- )
  latest @ begin ?dup while
    dup cell+ c@ 64 and 0= if dup name>string type space then  @
  repeat cr ;
