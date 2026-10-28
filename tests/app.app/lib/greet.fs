\ greet.fs: part of the test app
variable greeted
: greet  ( -- )  1 greeted +!  ." hello from the app" cr ;
: dir  ( -- )  ." the app's own dir" cr ;   \ shadows the base's, for the app and the console
