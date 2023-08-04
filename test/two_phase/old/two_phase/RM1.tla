------------------------------- MODULE RM1 ----------------------------- 

VARIABLES rmState

RmId == "rm1"

Init == rmState = "working"

SndPrepare1(rm) == 
  /\ rm = RmId
  /\ rmState = "working"
  /\ rmState' = "prepared"
  
SilentAbort1(rm) ==
  /\ rmState = "working"
  /\ rmState' = "aborted"

RcvCommit1(rm) ==
  /\ rm = RmId
  /\ rmState' = "committed"

RcvAbort1(rm) ==
  /\ rm = RmId
  /\ rmState' = "aborted"

TypeOK == rmState \in {"working", "prepared", "committed", "aborted"}

=============================================================================
