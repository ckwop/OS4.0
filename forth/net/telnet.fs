\ net/telnet.fs: a task's terminal on a TCP connection, speaking just enough
\ telnet. We offer to echo and to suppress go-ahead, which puts clients in
\ character mode: ACCEPT does the echoing and line editing, as on the serial
\ console. Every other option request is ignored. Line ends go out as CR LF;
\ CR LF and CR NUL come in as one CR.

255 constant iac
251 constant will              \ WILL WONT DO DONT are 251-254, then an option
250 constant sb                \ subnegotiation: SB ... IAC SE
240 constant se
1 constant opt-echo
3 constant opt-sga

user term-conn                 \ the connection this task's terminal is on
user after-cr                  \ the last character in was a CR

\ ---- Input

: conn-byte  ( -- c | -1 )  \ the next byte, waiting for it; -1 once input has ended
  term-conn @ cur-conn !  io-start                  \ throws -273 after IO-TIMEOUT idle
  begin
    cur-conn @ rx-unread if  cur-conn @ dup c.rx-out @ rx@  1 consumed exit  then
    cur-conn @ fin-received flag?  cur-conn @ c.state @ closed = or if  -1 exit  then
    io-wait
  again ;

: skip-subnegotiation  ( -- )
  begin
    conn-byte  dup -1 = if drop exit then
    iac = if  conn-byte  dup se =  swap -1 = or if exit then  then
  again ;
: telnet-command  ( -- c | -2 | -1 )  \ after IAC: a data byte 255, -2 for a command, or -1
  conn-byte
  dup -1 = if exit then
  dup iac = if exit then                          \ IAC IAC: the byte 255
  dup sb = if  drop skip-subnegotiation -2 exit  then
  will 255 within if  conn-byte -1 = if -1 else -2 then  exit  then
  -2 ;

: telnet-key  ( -- c )  \ -1 at the end of input
  begin
    conn-byte
    dup iac = if
      drop telnet-command
    else
      dup 10 =  over 0= or  after-cr @ and if drop -2 then   \ the CR was the line end
    then
    dup 13 = after-cr !
    dup -2 = while drop
  repeat ;
: telnet-key?  ( -- flag )
  term-conn @  dup rx-unread 0<>  over fin-received flag? or  swap c.state @ closed = or ;

\ ---- Output. Data goes out at once when nothing is waiting to be acknowledged,
\ and otherwise with the next acknowledgement (Nagle's rule), so that echoing
\ each key or printing a long line does not make a segment per character.

create iac-iac  iac c, iac c,
: special?  ( c -- flag )  dup 10 = swap iac = or ;
: plain  ( addr u -- n )  \ how many characters come before one needing translation
  tuck 0 ?do  dup i + c@ special? if  2drop i unloop exit  then  loop drop ;
: telnet-type  ( addr u -- )
  term-conn @ cur-conn !
  begin dup while
    2dup plain ?dup if
      >r over r@ (send) r> /string
    else
      over c@ 10 = if crlf else iac-iac then  2 (send)  1 /string
    then
  repeat 2drop
  cur-conn @ in-flight 0= if  cur-conn @ tcp-output  then ;

\ ---- Switching terminals

create character-mode  iac c, will c, opt-echo c,  iac c, will c, opt-sga c,
: telnet-terminal  ( conn -- )  \ this task's terminal is conn from now on
  dup term-conn !  0 after-cr !
  ['] telnet-type 'type !  ['] telnet-key 'key !  ['] telnet-key? 'key? !
  character-mode 6 rot send ;
: console-terminal  ( -- )  \ back to the console
  0 term-conn !
  ['] console-type 'type !  ['] console-key 'key !  ['] console-key? 'key? ! ;
