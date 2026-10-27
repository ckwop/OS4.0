\ net/net.fs: the network task, which takes frames from the interface and hands
\ them to ARP or IP, and words to look at the network.

: frame-in  ( len -- )
  1 frames-in +!
  dup /eth < if drop exit then
  rx-frame eth-type + n16@
  dup type-arp = if  drop rx-frame /eth + swap /eth - arp-in exit  then
  type-ipv4 = if  /eth - ip-in  else drop then ;

\ Handle every waiting frame, pausing between them; when none is waiting, sleep
\ until the next timer tick. A frame whose handling throws is dropped, and the
\ network carries on; so do the timers. Should the loop end anyway, RESTARTING
\ starts it again.
variable net-errors             \ frames or timer rounds that threw
: net-loop  ( -- )
  begin
    ['] tcp-timers catch if  1 net-errors +!  then
    rx-frame net-poll ?dup if
      ['] frame-in catch if  drop 1 net-errors +!  then  pause
    else  10 ms  then
  again ;

task net-task
: start-net  ( -- )  net-up? if  ['] net-loop ['] restarting net-task start-with  then ;
start-net

: .net  ( -- )
  net-up? 0= if -264 throw then
  ." ip " my-ip @ .ip  ."  mac " net-mac .mac  ."  gateway " gateway @ .ip ;
: .net-stats  ( -- )
  ." frames in " frames-in @ (.) type  ."  out " frames-out @ (.) type
  ." , ARP answered " arps-answered @ (.) type  ." , pings answered " echoes-answered @ (.) type ;
