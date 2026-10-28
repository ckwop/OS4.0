\ app.fs: the test app for tests/app.in, on a FAT32 app disk
include lib/greet.fs
: main  ( -- )  greet  ." main ran" cr ;
