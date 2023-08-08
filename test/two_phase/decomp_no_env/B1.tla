--------------------------- MODULE B1 ---------------------------


VARIABLES tmState, tmPrepared

vars == <<tmState,tmPrepared>>

RMs == {"rm1","rm2"}

Init ==
/\ tmState = "init"
/\ tmPrepared = {}

Prepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = tmPrepared \cup {rm}
/\ UNCHANGED <<tmState>>

Commit(rm) ==
/\ tmState \in {"init","commmitted"}
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>

Abort(rm) ==
/\ tmState \in {"init","aborted"}
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>

Next ==
\E rm \in RMs :
\/ Prepare(rm)
\/ Commit(rm)
\/ Abort(rm)

Spec == Init /\ [][Next]_vars
=============================================================================
