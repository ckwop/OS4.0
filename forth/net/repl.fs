\ net/repl.fs: the network REPL. Telnet to port 4000 for the sandbox, or to
\ 4001 for the full Forth after the admin password. Until a password is set
\ (on the console, with SET-ADMIN-PASSWORD), port 4001 turns everyone away.
\ Each port allows a few sessions at once; each session runs in a pooled task
\ of its own, until BYE, the end of input, the client going away, or
\ SESSION-IDLE ms without input.

4000 constant sandbox-port
4001 constant admin-port
998 constant admin-record       \ blocks 998 and 999: the admin password's hash
variable session-idle  600000 session-idle !    \ ms
variable sessions-served        \ sessions that have ended
variable sessions-refused       \ connections turned away because the door was full

\ ---- The admin password

create admin-pw  /password allot
: admin-password?  ( -- flag )  \ one is set: its hash is now in ADMIN-PW
  admin-pw /password admin-record ['] record@ catch if  2drop drop false exit  then
  /password = ;
: read-secret  ( -- addr len )  \ a line typed without echo, in PAD
  true hidden !  pad 64 accept  false hidden !  pad swap  cr ;
: forget-secret  ( -- )  pad 64 0 fill ;

create new-pw 64 allot
variable new-pw-len
: set-admin-password  ( -- )  \ asks for it twice, without echo, and stores its hash
  ." New admin password: " read-secret
  dup 0= if  2drop ." Not changed." cr exit  then
  dup new-pw-len !  new-pw swap move  forget-secret
  ." Again: " read-secret  new-pw new-pw-len @ compare  forget-secret
  if  new-pw 64 0 fill  ." They differ: not changed." cr exit  then
  new-pw new-pw-len @ admin-pw hash-password  new-pw 64 0 fill
  admin-pw /password admin-record record!
  ." Admin password set." cr ;

: login?  ( -- flag )  \ three tries at the admin password
  3 0 do
    ." Password: " read-secret admin-pw password?  forget-secret
    if true unloop exit then
    eof @ if false unloop exit then
    2000 ms  ." Wrong password." cr
  loop false ;

\ ---- Sessions

: end-session  ( -- )  true eof ! ;               \ BYE in a session
: greet  ( addr u -- )  ." OS 4.0 " type ." . Type bye to leave." cr ;
: sandbox-session  ( -- )  sandbox-wordlist 1 set-order  s" sandbox" greet ;
: admin-session  ( -- )
  admin-password? 0= if
    ." No admin password is set: set one on the console with set-admin-password." cr
    end-session exit
  then
  login? 0= if  ." Goodbye." cr end-session exit  then
  only  s" full Forth" greet ;

: (session)  ( setup-xt -- )  execute repl ;
: farewell  ( n -- )  cr .error ;                  \ why the session ended, if it can be told
: session  ( conn setup-xt -- )
  'bye @ >r
  swap telnet-terminal  0 eof !  ['] end-session 'bye !  0 state !  decimal
  session-idle @ io-timeout !
  ['] (session) catch ?dup if  ['] farewell catch if drop then  then
  reset  only  false hidden !  0 io-timeout !
  term-conn @  console-terminal  close-connection
  1 sessions-served +!  r> 'bye ! ;

\ ---- Doors: a port, the setup for its sessions, how many it allows and has

0
1 cells field door.port
1 cells field door.setup
1 cells field door.limit
1 cells field door.count
constant /door
create sandbox-door  sandbox-port , ' sandbox-session , 16 , 0 ,
create admin-door    admin-port , ' admin-session , 4 , 0 ,
: door-of  ( conn -- door )  c.lport @ admin-port = if admin-door else sandbox-door then ;

: run-session  ( conn -- )
  dup door-of >r  r@ door.setup @ session  -1 r> door.count +! ;
: turn-away  ( conn -- )  \ the door is full: say so, and close
  5000 io-timeout !
  dup >r  s" Too many sessions: try again later." r@ ['] send-line catch if drop 2drop then
  r> close-connection  0 io-timeout !  1 sessions-refused +! ;

\ A connection gets a task of its own, or one to turn it away if the door is
\ full; with no task to be had, it is reset.
: away  ( conn -- )
  dup ['] turn-away ['] spawn catch if  2drop drop-connection  else  2drop  then ;
: admit  ( conn door -- )
  dup door.count @  over door.limit @ < 0= if  drop away exit  then
  1 over door.count +!
  over ['] run-session ['] spawn catch
  if  2drop  -1 swap door.count +!  drop-connection  else  drop 2drop  then ;

: serve-door  ( door -- )  \ forever
  dup door.port @ listen
  begin  dup door.port @ accept-connection  over admit  again ;
: sandbox-doors  ( -- )  sandbox-door serve-door ;
: admin-doors    ( -- )  admin-door serve-door ;

task sandbox-listener
task admin-listener
: start-repl  ( -- )  \ the listeners are supervised: see RESTARTING
  net-up? if
    ['] sandbox-doors ['] restarting sandbox-listener start-with
    ['] admin-doors ['] restarting admin-listener start-with
  then ;
