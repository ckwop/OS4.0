\ dump-virt.fs: run before tools/dump-words.fs on the bare-metal build, which
\ has no system calls: its output goes to the console with CONSOLE-TYPE (not
\ TYPE, which the dump points at its own buffer), so the same dump comes out
\ over the serial line (V4).
0 constant sys-write
: syscall  ( fd addr u x n -- r )  2drop console-type drop 0 ;
