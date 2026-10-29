\ app.fs: the test app for tests/doors.in: a door of its own on port 5001,
\ which lets one session in at a time, and port 4001 without port 4000.
\ After a line, KEY? must be false: the LF of its CR LF is not a key.
: shout-session  ( -- )
  ." Say something." cr  pad 80 accept  ." You said: " pad swap type cr
  500 ms  ." Another key waiting: " key? . cr ;
5001 ' shout-session 1 port-door shout-door
: shout-doors  ( -- )  shout-door serve-door ;
task shout-listener
: main  ( -- )  ['] shout-doors ['] restarting shout-listener start-with  start-admin ;
