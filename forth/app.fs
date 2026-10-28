\ app.fs: starting the application, if the app disk holds one (DECISIONS.md
\ #99). An app is files on the app disk, and app.fs is its entry point. Its
\ words go in APP-WORDLIST, searched before the base's. Once app.fs has loaded,
\ MAIN runs if the app defined it: it starts the app's tasks and returns. An
\ error stops the app, never the boot: it is reported, and the console follows
\ either way. With no app, the base starts the network REPL itself.

wordlist constant app-wordlist

: app?  ( -- flag )  \ the app disk holds app.fs
  s" app.fs" r/o open-file if drop false else close-file drop true then ;
: (boot-app)  ( -- )
  s" app.fs" included
  s" main" app-wordlist search-wordlist if execute then ;
: boot-app  ( -- )
  forth-wordlist app-wordlist 2 set-order  app-wordlist set-current
  ['] (boot-app) catch  forth-wordlist set-current
  ?dup if  ." app: " .error reset  then ;
: start-app  ( -- )  app? if boot-app else start-repl then ;
