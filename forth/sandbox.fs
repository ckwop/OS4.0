\ sandbox.fs: the sandbox wordlist, a Forth for anyone. It can compute and
\ print, but cannot compile, reach memory, or find any word outside it: a
\ task whose search order is the sandbox alone sees nothing else.

wordlist constant sandbox-wordlist

\ EXPOSE puts a word into the sandbox as a new word that calls it, immediate
\ and compile-only as the original is. It switches CURRENT only while it runs,
\ so the kernel's boot-time lookups (which use LATEST) are not disturbed.
: expose  ( "name" -- )
  parse-name 2dup find-name ?dup 0= if undefined then       ( addr u nt )
  get-current >r  sandbox-wordlist set-current
  -rot header docol cf,  dup name>xt ,  ['] exit ,
  dup immediate? if immediate then
  compile-only? if compile-only then
  r> set-current ;

expose +      expose -      expose *      expose /      expose mod    expose /mod
expose negate expose abs    expose min    expose max    expose 1+     expose 1-
expose 2*     expose and    expose or     expose xor    expose invert
expose lshift expose rshift
expose =      expose <>     expose <      expose >      expose 0=     expose 0<
expose u<
expose dup    expose drop   expose swap   expose over   expose rot    expose nip
expose tuck   expose 2dup   expose 2drop  expose depth
expose .      expose u.     expose .s     expose cr     expose emit   expose space
expose spaces expose ."     expose .(     expose (      expose \
expose hex    expose decimal              expose words  expose bye
