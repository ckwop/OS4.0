\ interpreter.fs: the outer interpreter and the REPL.
\ Loaded last: the kernel's assembly interpreter loads the boot files, and the
\ end of this file hands the terminal to QUIT below, so the REPL is Forth.

\ ---- Tools

: source  ( -- addr u )  'tib @ #tib @ ;
: lower   ( c -- c' )  dup [char] A [char] Z 1+ within if 32 + then ;
: hidden?    ( nt -- flag )  cell+ c@ f-hidden and 0<> ;
: immediate? ( nt -- flag )  cell+ c@ f-immediate and 0<> ;

\ ---- Wordlists. A wordlist is a cell holding its newest word. New definitions
\ go into the CURRENT wordlist, whose newest word is kept in the kernel's
\ LATEST while it is current. Each task has its own search order: lookups try
\ its wordlists first to last, and see nothing else.

create forth-wordlist  0 ,
variable current   forth-wordlist current !
8 constant max-order
-49 message: search order full
user #order
max-order user-cells context                     \ the search order, first one first
forth-wordlist context !  1 #order !             \ the console's; new tasks copy it

: wid-latest   ( wid -- nt | 0 )  dup current @ = if drop latest @ else @ then ;
: get-current  ( -- wid )  current @ ;
: set-current  ( wid -- )  claim  latest @ current @ !  dup current !  @ latest ! ;
: wordlist     ( -- wid )  here 0 , ;
: order@       ( i -- wid )  cells context + @ ;
: get-order    ( -- widn ... wid1 n )  #order @ 0 ?do  #order @ i - 1- order@  loop  #order @ ;
: set-order    ( widn ... wid1 n -- )  \ -1: the minimum, FORTH-WORDLIST alone
  dup -1 = if drop forth-wordlist 1 then
  dup max-order u> if -49 throw then
  dup #order !  0 ?do  i cells context + !  loop ;
: only         ( -- )  -1 set-order ;
: also         ( -- )  get-order over swap 1+ set-order ;
: previous     ( -- )  get-order nip 1- set-order ;
: forth        ( -- )  get-order nip forth-wordlist swap set-order ;
: definitions  ( -- )  context @ set-current ;
: words  ( -- )  \ the first wordlist in the search order
  #order @ 0= if exit then
  context @ wid-latest begin ?dup while
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
\ SEARCH-LIST ( addr u nt -- nt | 0 ) is in the kernel for speed; this is its
\ definition. It looks from nt back to the oldest word of its wordlist.
: search-list-ref  ( addr u nt -- nt | 0 )
  begin dup while
    >r 2dup r@ match? if  2drop r> exit  then
    r> @
  repeat nip nip ;
: find-name  ( addr u -- nt | 0 )  \ in the search order
  #order @ 0 ?do
    2dup i order@ wid-latest search-list ?dup if  nip nip unloop exit  then
  loop 2drop 0 ;
: >found  ( nt | 0 -- 0 | xt 1 | xt -1 )  dup if  dup name>xt swap immediate? if 1 else -1 then  then ;
: find-word  ( addr u -- 0 | xt 1 | xt -1 )  find-name >found ;  \ 1 if immediate
: search-wordlist  ( addr u wid -- 0 | xt 1 | xt -1 )  wid-latest search-list >found ;
: compile-only?  ( nt -- flag )  cell+ c@ f-compile-only and 0<> ;

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

: undefined  ( addr u -- )  errname 2! -13 throw ;
: ?stack     ( -- )  \ overflows are caught as they happen, underflows here
  depth 0< if -4 throw then  rp@ task-r0 @ u> if -6 throw then ;
: interpret  ( -- )  \ the current line, word by word
  begin parse-name dup while
    2dup find-name ?dup if
      state @ 0= over compile-only? and if  drop errname 2! -14 throw  then
      nip nip  dup immediate? state @ 0= or if name>xt execute else name>xt , then
    else
      2dup number? 0= if undefined then  nip nip  state @ if postpone literal then
    then ?stack
  repeat 2drop ;
' interpret 'interpret !   \ for LOAD

\ Words that look names up for the user, rebuilt on FIND-WORD so that every
\ lookup after boot goes through it (wordlists will change only FIND-NAME).
\ The kernel's versions are only for loading the boot files.
: parse-find  ( "name" -- xt 1 | xt -1 )  \ throws if the word is not found
  parse-name dup 0= if -16 throw then
  2dup find-word ?dup if  2swap 2drop  else  undefined  then ;
: '         ( "name" -- xt )  parse-find drop ;
: [']       ( "name" -- )  ' postpone literal ; immediate compile-only
: postpone  ( "name" -- )
  parse-find 0< if  postpone literal  ['] , ,  else  ,  then ; immediate compile-only

\ Terminal input. The Forth echoes what is typed: neither a serial console nor
\ a telnet session in character mode does. KEY lets other tasks run while waiting.
user eof                        \ the terminal's input has ended
user hidden                     \ ACCEPT does not echo: for passwords
: rubout  ( -- )  hidden @ if exit then  8 emit space 8 emit ;
: accept  ( addr max -- u )  \ Enter ends the line; Ctrl-D on an empty line ends input
  >r 0 begin key
    dup 10 = over 13 = or if drop space nip r> drop exit then
    dup -1 = if drop true eof ! dup if space then nip r> drop exit then
    dup 4 = if drop dup 0= if true eof ! nip r> drop exit then 0 then
    dup 9 = if drop bl then
    dup 8 = over 127 = or if drop dup if 1- rubout then 0 then
    dup bl < if drop else
      over r@ < if  >r 2dup + r@ swap c! 1+ r> hidden @ if drop else emit then  else drop then
    then
  again ;
-271 message: end of input
: refill  ( -- flag )  \ the next line from the terminal; false at the end of input
  eof @ if false exit then
  tib 'tib !  tib /tib accept  dup #tib !  0 >in !
  0= eof @ and 0= ;
: prompt  ( -- )  state @ if ."  compiled" else ."  ok" then cr ;
: reset   ( i*x -- )  begin depth while drop repeat  0 state !  0 error-blk !  unclaim ;

\ The REPL. Each line runs under CATCH: an error is reported, then the next
\ line. The dictionary is given up between lines unless a definition is open.
: repl  ( -- )  \ until the end of input
  unclaim
  begin refill while
    ['] interpret catch ?dup if .error reset else prompt then
    state @ 0= if unclaim then
  repeat reset ;

\ BYE ends this task's terminal session: on the console it shuts the system down.
user 'bye   ' bye 'bye !
: bye  ( -- )  'bye @ execute ;
: (quit)  ( -- )  repl bye ;
' (quit) 'quit !
