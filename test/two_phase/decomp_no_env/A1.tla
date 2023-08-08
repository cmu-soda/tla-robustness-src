--------------------------- MODULE A1 ---------------------------


VARIABLES rmState

vars == <<rmState>>

RMs == {"rm1","rm2"}

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

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")
=============================================================================
