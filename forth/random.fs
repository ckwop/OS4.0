\ random.fs: SipHash-2-4, a keyed hash, and random numbers from it. SipHash
\ (Aumasson and Bernstein, 2012) turns a message and a 128-bit secret key into
\ 64 bits that cannot be predicted without the key. It keys TCP's initial
\ sequence numbers and hash tables that outsiders choose entries for; RANDOM is
\ SipHash of a counter, under a key drawn from the entropy HAL at boot.

: rotl  ( x n -- x' )  \ rotate a cell left by n bits, 0 < n < 64
  2dup lshift -rot 64 swap - rshift or ;

\ SipHash's state. It never pauses, so one copy serves every task.
variable v0  variable v1  variable v2  variable v3

: sipround  ( -- )
  v1 @ v0 +!  v1 @ 13 rotl v0 @ xor v1 !  v0 @ 32 rotl v0 !
  v3 @ v2 +!  v3 @ 16 rotl v2 @ xor v3 !
  v3 @ v0 +!  v3 @ 21 rotl v0 @ xor v3 !
  v1 @ v2 +!  v1 @ 17 rotl v2 @ xor v1 !  v2 @ 32 rotl v2 ! ;
: sip-word  ( m -- )  dup v3 @ xor v3 !  sipround sipround  v0 @ xor v0 ! ;

: siphash  ( addr u k0 k1 -- h )  \ the 64-bit SipHash-2-4 of the bytes at addr
  dup $646f72616e646f6d xor v1 !  $7465646279746573 xor v3 !
  dup $736f6d6570736575 xor v0 !  $6c7967656e657261 xor v2 !
  dup 56 lshift >r                                  \ the length's low byte, at the top
  begin dup 8 < 0= while  over @ sip-word  8 /string  repeat
  r> -rot 0 ?do  dup i + c@ i 8 * lshift rot or swap  loop drop
  sip-word
  v2 @ $ff xor v2 !  sipround sipround sipround sipround
  v0 @ v1 @ xor v2 @ xor v3 @ xor ;

\ ---- Random numbers

create random-key  0 , 0 ,
variable drawn                         \ how many numbers RANDOM has made

: random  ( -- u )  \ 64 random bits
  1 drawn +!  drawn 8 random-key @ random-key cell+ @ siphash ;
: random-key2  ( -- k0 k1 )  \ a fresh secret key, for SIPHASH
  random random ;

: seed-random  ( -- )  \ the key from the hardware, or (much weaker) from the clock
  random-key 16 ['] entropy catch if
    2drop  counter random-key !  counter 29 rotl random-key cell+ !
    ." warning: no entropy source; random numbers are predictable" cr
  then ;
seed-random
