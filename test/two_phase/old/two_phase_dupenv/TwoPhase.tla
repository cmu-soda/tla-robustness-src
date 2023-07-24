------------------------------- MODULE TwoPhase ----------------------------- 

VARIABLES tmState, tmPrepared, rmState

vars == <<tmState, tmPrepared, rmState>>

RMs == {"rm1", "rm2"}


Init ==   
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ rmState = [rm \in RMs |-> "working"]


\* TM transitions

TMPrepare(rm) ==
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState, rmState>>

TMCommit(rm) ==
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState>>

TMAbort(rm) ==
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState>>


\* RM transitions

RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RMCommit(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RMAbort(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared>>
  
RMSilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared>>


Prepare(rm) == TMPrepare(rm) /\ RMPrepare(rm)
Commit(rm) == TMCommit(rm) /\ RMCommit(rm)
Abort(rm) == TMAbort(rm) /\ RMAbort(rm)
SilentAbort(rm) == RMSilentAbort(rm)

PrepareEvil(rm) ==
    \/ TMPrepare(rm)
    \/ RMPrepare(rm)
CommitEvil(rm) ==
    \/ TMCommit(rm)
    \/ RMCommit(rm)
AbortEvil(rm) ==
    \/ TMAbort(rm)
    \/ RMAbort(rm)


Next ==
    \E rm \in RMs :
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \/ SilentAbort(rm)
        \/ PrepareEvil(rm)
        \/ CommitEvil(rm)
        \/ AbortEvil(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

=============================================================================
