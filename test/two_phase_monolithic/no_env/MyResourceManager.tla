------------------------------- MODULE ResourceManager ----------------------------- 

VARIABLES rmState

vars == <<rmState>>

RMs == {"rm1"}


Init ==   
  /\ rmState = [rm \in RMs |-> "working"]

Prepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]

Commit(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]

Abort(rm) ==
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]


Next ==
    \E rm \in RMs :
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]

=============================================================================
