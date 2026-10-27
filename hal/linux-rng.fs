\ linux-rng.fs: the entropy HAL for the hosted build, from getrandom(2).
\   entropy  ( addr u -- )  fill addr with u bytes of hardware randomness

278 constant sys-getrandom
-272 message: no entropy source

: entropy  ( addr u -- )  \ getrandom may give fewer bytes than asked: ask again
  begin dup while
    2dup 0 0 sys-getrandom syscall
    dup 0> 0= if  drop 2drop -272 throw  then
    /string
  repeat 2drop ;
