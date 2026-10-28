\ dump-words.fs: print every word in the dictionary as compiled, for
\ tools/forth2lean.py. Fed to the hosted build's console by make dump-words.
\ Each word is one line, numbers in decimal: "@@ xt kind name cells...", where
\ kind is 0 primitive, 1 colon, 2 constant, 3 variable, 4 other (a DOES> child).
\ A colon word's cells are its whole thread; a constant's, its value. A body
\ ends where the next newer header starts, so nothing here decodes threads.

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
  2 = if cell+ @ u. else drop then ;
: dump-words  ( -- )
  here limit !  latest @ begin ?dup while  dup .word  dup limit !  @ pause repeat
  cr ." @@ end" cr ;                               \ the dump is complete
dump-words
