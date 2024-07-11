--------------------------- MODULE C2 ---------------------------


VARIABLES server_holds_lock

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<server_holds_lock>>

RecvLock(n) ==
/\ server_holds_lock
/\ server_holds_lock' = FALSE

RecvUnlock(n) ==
/\ server_holds_lock' = TRUE

Next ==
\/ (\E n \in Node : RecvLock(n))
\/ (\E n \in Node : RecvUnlock(n))

Init ==
/\ server_holds_lock = TRUE

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (server_holds_lock \in BOOLEAN)
=============================================================================
