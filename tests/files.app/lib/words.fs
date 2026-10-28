\ words.fs: included by files.in
: square  ( n -- n2 )  dup * ;
include lib/nested.fs
: cube  ( n -- n3 )
  dup square
  * ;
: sum-to  ( n -- sum )  \ a definition with a loop across lines
  0 swap 1+ 1 ?do
    i +
  loop ;
