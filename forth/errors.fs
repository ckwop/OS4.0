\ errors.fs: reporting errors that reach the outer interpreter, or the top of a
\ task. Codes without special handling print the text registered with MESSAGE:.

2 user-cells errname          \ ( addr len ) the word an error is about; per task
user error-line               \ where an error in an INCLUDEd file happened, for .ERROR
4 user-cells error-file       \ ... a counted string: the end of the file's name

: .where  ( -- )  \ "block 20 line 3: " or "app.fs:3: " if the error was in a block or a file
  error-line @ ?dup if  error-file count type [char] : emit (.) type ." : " exit  then
  error-blk @ ?dup if
    ." block " (.) type ."  line " error-in @ 1- 0 max 64 / (.) type ." : "
  then ;
: .error  ( n -- )
  dup -1 = over -256 = or if drop exit then   \ ABORT; a CPU fault has its own report
  .where
  dup -2 = if drop abort-msg 2@ type cr exit then
  dup -13 = if drop errname 2@ type ."  ?" cr exit then
  dup -14 = if drop errname 2@ type ."  is compile-only" cr exit then
  dup message if type cr drop exit then
  ." error " (.) type cr ;
