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

user pooled                                       \ true for a task from the pool (SPAWN)
user next-free                                    \ the next task in the pool's free list
0 pooled !

/user /dstack + /rstack + /buffers + constant /task

: new-task  ( name len -- task )  \ a task, asleep, at the end of the ring
  /task reserve >r                                \ not from the dictionary: see CLAIM
  up@ r@ /user move                               \ start from a copy of this task's
  r@ /user + /dstack +  dup r@ task-s0 field!
  /rstack +             dup r@ task-r0 field!
                        r@ task-buffers field!    \ PAD and the rest (output.fs)
  r@ /user + 16 cells +            r@ task-slimit field!   \ room to report an overflow
  r@ task-s0 >user @ 16 cells +    r@ task-rlimit field!
  1 r@ task-status field!  0 r@ task-wake field!
  0 r@ handler field!  0 r@ blk field!  0 r@ state field!  0 r@ pooled field!
  r@ task-name >user 2!
  main-task r@ task-link field!
  r@ last-task link-of !
  r> ;

: task  ( "name" -- )  \ define a named task, asleep; name ( -- task )
  create  latest @ name>string new-task ,  does> @ ;

\ ---- Running and stopping tasks

: stop   ( -- )  1 task-status !  0 task-wake !  pause ;   \ until another task wakes this one
: wake   ( task -- )  0 swap task-status field! ;
: sleep  ( task -- )  dup 1 swap task-status field!  0 swap task-wake field! ;
: ms     ( n -- )  counter-hz 1000 / *  counter +  task-wake !  1 task-status !  pause ;
: stop-until  ( u -- )  task-wake !  1 task-status !  pause ;  \ until woken or counter value u

variable free-tasks                                \ pooled tasks with nothing to do

: report  ( n -- )  task-name 2@ type ." : " .error ;
: run-task  ( i*x xt -- )  \ a task's whole life: run xt, report how it ended, sleep
  catch ?dup if  ['] report catch if drop then  then   \ its terminal may be gone
  unclaim  0 state !
  pooled @ if  free-tasks @ next-free !  up@ free-tasks !  then   \ back to the pool
  begin stop again ;
create task-thread  ' run-task ,                 \ where a started task begins

: (start)  ( x xt task cells -- )  \ the task's stack: x if cells is 3, then xt on top
  over up@ = if -24 throw then
  swap >r  r@ task-s0 >user @  swap cells -               ( x xt sp )
  tuck !  tuck cell+ !  r@ task-sp field!   \ xt on top; x below it (unused when cells is 2)
  task-thread  r@ task-r0 >user @  1 cells -  tuck !  r@ task-rp field!
  0 r@ handler field!  0 r@ task-wake field!  0 r@ task-status field!
  r> drop ;
: start       ( xt task -- )    \ run xt in task, from empty stacks
  0 -rot 2 (start) ;
: start-with  ( x xt task -- )  \ run xt in task with x on its stack
  3 (start) ;

\ ---- The pool: tasks made on demand, reused once their work is done. There is
\ no limit but memory (DECISIONS.md #71).

: spawn  ( x xt -- task )  \ run xt with x in a pooled task
  free-tasks @ ?dup if
    dup next-free >user @ free-tasks !
  else
    s" worker" new-task  true over pooled field!
  then
  dup >r start-with r> ;

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
: console-key  ( -- c )  pause  begin console-key? 0= while 10 ms repeat (console-key) ;
' console-key 'key !
