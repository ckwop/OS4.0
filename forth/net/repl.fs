\ net/repl.fs: the network REPL. Telnet to port 4000 for the sandbox, or to
\ 4001 for the full Forth (the operator's: never to be reachable from the
\ internet until it has a login; docs/tech-debt.md TD-23). Each session runs
\ in a pooled task of its own, until BYE, the end of input, or the client
\ going away.

4000 constant sandbox-port
4001 constant admin-port

: end-session  ( -- )  true eof ! ;               \ BYE in a session
: greet  ( addr u -- )  ." OS 4.0 " type ." . Type bye to leave." cr ;
: sandbox-session  ( -- )  sandbox-wordlist 1 set-order  s" sandbox" greet ;
: admin-session    ( -- )  only  s" full Forth" greet ;

: (session)  ( setup-xt -- )  execute repl ;
: session  ( conn setup-xt -- )
  'bye @ >r
  swap telnet-terminal  0 eof !  ['] end-session 'bye !  0 state !  decimal
  ['] (session) catch if drop then                \ the client has gone, or worse
  reset  only
  term-conn @  console-terminal  close-connection
  r> 'bye ! ;
: sandbox-run  ( conn -- )  ['] sandbox-session session ;
: admin-run    ( conn -- )  ['] admin-session session ;

: serve-port  ( port xt -- )  \ forever: each connection to port runs xt in a task of its own
  swap dup listen
  begin  dup accept-connection  2 pick spawn drop  again ;
: sandbox-doors  ( -- )  sandbox-port ['] sandbox-run serve-port ;
: admin-doors    ( -- )  admin-port ['] admin-run serve-port ;

task sandbox-listener
task admin-listener
: start-repl  ( -- )
  net-up? if
    ['] sandbox-doors sandbox-listener start
    ['] admin-doors admin-listener start
  then ;
start-repl
