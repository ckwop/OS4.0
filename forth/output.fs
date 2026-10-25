\ output.fs: terminal output, number output and strings.
\ Loaded after core.fs.

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

