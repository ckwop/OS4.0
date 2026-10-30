\ dump-words.fs: print every word in the dictionary as compiled, for
\ tools/forth2lean.py. Fed to the hosted build's console by make dump-words.
\ Each word is one line, numbers in decimal: "@@ xt kind name cells...", where
\ kind is 0 primitive, 1 colon, 2 constant, 3 variable, 4 other (a DOES> child).
\ A colon word's cells are its whole thread; a constant's, its value; a DOES>
\ child's, where its code field branches to. A body ends where the next newer
\ header starts, so nothing here decodes threads. First comes "@@ top addr",
\ the end of the dictionary's space, below which RESERVE takes memory.

: bl-target  ( xt -- addr | 0 )  \ where the bl in a code field goes, 0 if none
  4 +  dup l@  dup $fc000000 and $94000000 <> if 2drop 0 exit then
  $3ffffff and  dup $2000000 and if $3ffffff invert or then  2 lshift + ;
: kind  ( xt -- n )
  dup l@ $d503201f <> if drop 0 exit then         \ code fields start with nop
  bl-target  dup docol = if drop 1 exit then
  dup docon = if drop 2 exit then  dovar = if 3 else 4 then ;

variable limit                                    \ the end of the word being dumped
: .cells  ( addr -- )  begin dup limit @ u< while  dup @ u.  cell+ repeat drop ;
: .word  ( nt -- )
  cr ." @@ "  dup name>xt  dup u.  dup kind dup .  rot name>string type space
  dup 1 = if drop cell+ .cells exit then
  dup 4 = if drop bl-target u. exit then           \ where its DOES> code is
  2 = if cell+ @ u. else drop then ;
\ The console writes a character at a time, a system call each, which is slow
\ under emulation: collect the output and write it to stdout in blocks. The
\ buffer and its count are reserved, away from code (see output.fs).
4096 constant /out
/out cell+ reserve constant #out
: out  ( -- addr )  #out cell+ ;
: flush-out  ( -- )  1 out #out @ 0 sys-write syscall drop  0 #out ! ;
: out-type  ( addr u -- )
  dup #out @ + /out > if flush-out then
  tuck out #out @ + swap cmove  #out +! ;

: dump-words  ( -- )
  0 #out !  ['] out-type 'type !
  cr ." @@ top " dict-top u.                       \ where reserved memory ends
  here limit !  latest @ begin ?dup while  dup .word  dup limit !  @ pause repeat
  cr ." @@ end" cr  flush-out  ['] console-type 'type ! ;  \ the dump is complete
dump-words
