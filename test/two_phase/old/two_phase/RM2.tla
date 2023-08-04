------------------------------- MODULE RM2 ----------------------------- 

VARIABLES rmState

RmId == "rm2"

Init == rmState = "working"

SndPrepare2(rm) == 
  /\ rm = RmId
  /\ rmState = "working"
  /\ rmState' = "prepared"
  
SilentAbort2(rm) ==
  /\ rmState = "working"
  /\ rmState' = "aborted"

RcvCommit2(rm) ==
  /\ rm = RmId
  /\ rmState' = "committed"

RcvAbort2(rm) ==
  /\ rm = RmId
  /\ rmState' = "aborted"

TypeOK == rmState \in {"working", "prepared", "committed", "aborted"}

=============================================================================
