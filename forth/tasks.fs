\ tasks.fs: cooperative multitasking. A task is a user area plus its own data
\ and return stacks, linked into a ring that PAUSE (in the kernel) runs round.
\ The console is MAIN-TASK; others are defined with TASK and given work with
\ START. Every word that waits loops on PAUSE, or sleeps: a sleeping task is
\ skipped until its wake time or until another task WAKEs it, and when every
\ task sleeps the CPU idles until the next timer tick.
\ The watchdog makes a task that runs too long without pausing throw -262.

-262 message: stopped by the watchdog: it ran too long without pausing

256 cells constant /dstack
256 cells constant /rstack

: >user   ( task addr -- addr' )  up@ - + ;     \ the same user variable in another task
: field!  ( x task addr -- )  >user ! ;
: link-of ( task -- addr )  task-link >user ;

: last-task  ( -- task )  \ the task before the console in the ring
  main-task begin dup link-of @ dup main-task <> while nip repeat drop ;

: task  ( "name" -- )  \ define a task, asleep, at the end of the ring
  create  here >r  /user /dstack + /rstack + allot
  up@ r@ /user move                               \ start from a copy of this task's
  r@ /user + /dstack +  dup r@ task-s0 field!
  /rstack +             r@ task-r0 field!
  r@ /user + 16 cells +            r@ task-slimit field!   \ room to report an overflow
  r@ task-s0 >user @ 16 cells +    r@ task-rlimit field!
  1 r@ task-status field!  0 r@ task-wake field!
  0 r@ handler field!  0 r@ blk field!  0 r@ state field!
  latest @ name>string  r@ task-name >user 2!
  main-task r@ task-link field!
  r@ last-task link-of !
  r> drop ;

\ ---- Running and stopping tasks

: stop   ( -- )  1 task-status !  0 task-wake !  pause ;   \ until another task wakes this one
: wake   ( task -- )  0 swap task-status field! ;
: sleep  ( task -- )  dup 1 swap task-status field!  0 swap task-wake field! ;
: ms     ( n -- )  counter-hz 1000 / *  counter +  task-wake !  1 task-status !  pause ;

: run-task  ( xt -- )  \ a task's whole life: run xt, report how it ended, sleep
  catch ?dup if  task-name 2@ type ." : " .error  then
  begin stop again ;
create task-thread  ' run-task ,                 \ where a started task begins

: start  ( xt task -- )  \ run xt in task, from empty stacks
  dup up@ = if -24 throw then
  >r
  r@ task-s0 >user @  2 cells -  tuck !  r@ task-sp field!      \ xt will be on top
  task-thread  r@ task-r0 >user @  1 cells -  tuck !  r@ task-rp field!
  0 r@ handler field!  0 r@ task-wake field!  0 r@ task-status field!
  r> drop ;

\ ---- Looking at tasks

: .task  ( task -- )
  dup task-name >user 2@ type space
  dup up@ = if drop ." running" exit then
  dup task-status >user @ 0= if drop ." ready" exit then
  task-wake >user @ if ." sleeping" else ." stopped" then ;
: .tasks  ( -- )
  main-task begin  dup .task cr  link-of @  dup main-task = until drop ;

\ ---- The watchdog and the terminal

: watchdog  ( ms -- )  counter-hz 1000 / *  watchdog-limit ! ;   \ 0 turns it off
5000 watchdog

\ Others run while we wait. The timer ticks every 10 ms, so polling more often
\ would not help; a receive interrupt could replace the polling later. It
\ always pauses once, so a burst of typed or pasted input still lets other
\ tasks run, and never looks to the watchdog like a task that will not pause.
: key  ( -- c )  pause  begin key? 0= while 10 ms repeat key ;
