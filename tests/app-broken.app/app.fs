\ app.fs: the test app for tests/app-broken.in, which fails to load
: half  ( -- )  ." half" cr ;
nonsense
: main  ( -- )  ." main must not run" cr ;
