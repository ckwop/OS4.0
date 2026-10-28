\ start.fs: the last boot file. It starts the app, or the network REPL if there
\ is none, then hands the console to the Forth REPL; from here on, the
\ kernel's QUIT runs the loop in interpreter.fs.

.( OS 4.0) cr
start-app
quit
