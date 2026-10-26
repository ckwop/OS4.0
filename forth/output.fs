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
: (.)    ( n -- addr u )  dup >r abs 0 <# #s r> sign #> ;
: .      ( n -- )  (.) type space ;
: .r     ( n width -- )  >r (.) r> over - spaces type ;  \ right-aligned
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
create abort-msg 0 , 0 ,     \ ( addr u ) of the last ABORT" message
: (abort")  ( flag addr u -- )  rot if abort-msg 2! -2 throw then 2drop ;
: abort"  ( flag "ccc<quote>" -- )  postpone s" postpone (abort") ; immediate compile-only
: char    ( "name" -- c )  parse-name drop c@ ;
: [char]  ( "name" -- )  char postpone literal ; immediate compile-only
: -trailing  ( addr u -- addr u' )  \ without trailing spaces or control characters
  begin dup while  2dup + 1- c@ bl > 0= while  1-  repeat then ;

\ ---- Messages for THROW codes. Each module registers text for its own codes
\ with MESSAGE:, and the outer interpreter's .ERROR looks them up.
\ An entry: link, code, length, text.

variable messages
: message:  ( n "text" -- )  \ the rest of the line is the message
  align here  messages @ ,  messages !  ,
  0 parse  dup ,  here swap dup allot cmove  align ;
: message  ( n -- addr u true | false )
  messages @ begin dup while
    2dup cell+ @ = if  nip 2 cells + dup cell+ swap @ true exit  then
    @
  repeat nip ;

-3 message: stack overflow
-4 message: stack underflow
-5 message: return stack overflow
-6 message: return stack underflow
-8 message: dictionary full
-10 message: division by zero
-11 message: result out of range
-16 message: missing name
-19 message: name too long
-24 message: invalid numeric argument
-267 message: no room for another user variable

