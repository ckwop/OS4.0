\ app.fs: hello, the example OS 4.0 app. It greets whoever connects to TCP
\ port 5000, counting them, and hangs up. Its words go in APP-WORDLIST; MAIN
\ starts its task and returns, and the console follows.

include greeting.fs

5000 constant hello-port
variable greeted

: greet  ( conn -- )
  1 greeted +!
  greeting 2 pick send  greeted @ (.) 2 pick send-line
  close-connection ;
: greeter  ( -- )  \ for ever: RESTARTING runs it again if it ends
  5000 io-timeout !                     \ a client that stops reading is given up
  hello-port listen
  begin
    hello-port accept-connection  dup ['] greet catch if  drop drop-connection  else drop then
  again ;

task hello-task
: main  ( -- )
  ['] greeter ['] restarting hello-task start-with
  ." hello: listening on port " hello-port (.) type cr ;
