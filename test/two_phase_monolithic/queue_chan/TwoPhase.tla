------------------------------- MODULE TwoPhase ----------------------------- 

VARIABLES tmState, tmPrepared, rmState

vars == <<tmState, tmPrepared, rmState>>

RMs == {"rm1", "rm2"}


Init ==   
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ rmState = [rm \in RMs |-> "working"]


\* TM transitions

RcvPrepare(rm) ==
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState, rmState>>

SndCommit(rm) ==
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState>>

SndAbort(rm) ==
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState>>


\* RM transitions

SndPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RcvCommit(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RcvAbort(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared>>
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared>>


Next ==
    \E rm \in RMs :
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ SndAbort(rm)
        \/ SndPrepare(rm)
        \/ RcvCommit(rm)
        \/ RcvAbort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

=============================================================================
