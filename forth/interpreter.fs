\ interpreter.fs: the outer interpreter and the REPL.
\ Loaded last: the kernel's assembly interpreter loads the boot files, and the
\ end of this file hands the terminal to QUIT below, so the REPL is Forth.

\ ---- Tools

: source  ( -- addr u )  'tib @ #tib @ ;
: /string ( addr u n -- addr+n u-n )  tuck - >r + r> ;
: lower   ( c -- c' )  dup [char] A [char] Z 1+ within if 32 + then ;
: hidden?    ( nt -- flag )  cell+ c@ 64 and 0<> ;
: immediate? ( nt -- flag )  cell+ c@ 128 and 0<> ;
: words   ( -- )
  latest @ begin ?dup while
    dup hidden? 0= if dup name>string type space then  @
  repeat cr ;

\ ---- Parsing the current line

: end?    ( -- flag )  >in @ #tib @ < 0= ;
: char@   ( -- c )  source drop >in @ + c@ ;
: parse-name  ( "name" -- addr u )
  begin end? 0= while char@ bl > 0= while 1 >in +! repeat then
  source drop >in @ +
  begin end? 0= while char@ bl > while 1 >in +! repeat then
  source drop >in @ + over -
  end? 0= if 1 >in +! then ;
: parse   ( char "ccc<char>" -- addr u )
  >r source drop >in @ +
  begin end? 0= while char@ r@ <> while 1 >in +! repeat then
  r> drop  source drop >in @ + over -
  end? 0= if 1 >in +! then ;

\ Dictionary lookup, newest word first, ignoring case and hidden words.
: name=   ( addr1 addr2 u -- flag )
  0 ?do  over i + c@ lower  over i + c@ lower <> if 2drop false unloop exit then  loop
  2drop true ;
: match?  ( addr u nt -- flag )
  dup hidden? if drop 2drop false exit then
  name>string rot over <> if drop 2drop false exit then  name= ;
: find-word  ( addr u -- 0 | xt 1 | xt -1 )  \ 1 if immediate
  latest @ begin dup while
    >r 2dup r@ match? if  2drop r> dup name>xt swap immediate? if 1 else -1 then exit  then
    r> @
  repeat nip nip ;

\ Numbers: optional -, optional base prefix ($ hex, # decimal, % binary), digits;
\ or a character literal such as 'A'.
: digit?  ( c -- u true | false )
  lower dup [char] 0 [char] 9 1+ within if [char] 0 - else
  dup [char] a [char] z 1+ within if 87 - else drop false exit then then
  dup base @ < if true else drop false then ;
: prefix-base  ( c -- base | 0 )
  dup [char] $ = if drop 16 exit then
  dup [char] # = if drop 10 exit then
  [char] % = if 2 else 0 then ;
: (number)  ( addr u -- n true | false )  \ digits only, in the current base
  dup 0= if 2drop false exit then
  0 -rot begin dup while
    over c@ digit? 0= if 2drop drop false exit then
    >r rot base @ * r> + -rot 1 /string
  repeat 2drop true ;
: number?  ( addr u -- n true | false )
  dup 3 = if  over c@ [char] ' = if  over 2 + c@ [char] ' = if  drop 1+ c@ true exit  then then then
  over c@ [char] - = dup >r if 1 /string then
  dup 0= if 2drop r> drop false exit then
  over c@ prefix-base ?dup if  base @ >r base ! 1 /string (number) r> base !  else (number) then
  if r> if negate then true else r> drop false then ;

: undefined  ( addr u -- )  type ."  ?" cr abort ;
: ?stack     ( -- )  depth 0< if ." stack underflow" cr abort then ;
: interpret  ( -- )  \ the current line, word by word
  begin parse-name dup while
    2dup find-word ?dup if
      2swap 2drop  state @ if 0< if , else execute then else drop execute then
    else
      2dup number? 0= if undefined then  nip nip  state @ if postpone literal then
    then ?stack
  repeat 2drop ;

\ Terminal input. The Forth echoes what is typed: a serial console does not.
variable eof
: rubout  ( -- )  8 emit space 8 emit ;
: accept  ( addr max -- u )  \ Enter ends the line; Ctrl-D or end of input on an empty line: bye
  eof @ if bye then
  >r 0 begin key
    dup 10 = over 13 = or if drop space nip r> drop exit then
    dup -1 = if drop dup 0= if bye then true eof ! space nip r> drop exit then
    dup 4 = if drop dup 0= if bye then 0 then
    dup 9 = if drop bl then
    dup 8 = over 127 = or if drop dup if 1- rubout then 0 then
    dup bl < if drop else
      over r@ < if  >r 2dup + r@ swap c! 1+ r> emit  else drop then
    then
  again ;
create tib 256 allot
: refill  ( -- )  tib 'tib !  tib 256 accept #tib !  0 >in ! ;
: prompt  ( -- )  state @ if ."  compiled" else ."  ok" then cr ;
: (quit)  ( -- )  begin refill interpret prompt again ;

' (quit) 'quit !
.( OS 4.0) cr
quit
