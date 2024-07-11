--------------------------- MODULE C4 ---------------------------


VARIABLES unlock_msg

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<unlock_msg>>

Unlock(n) ==
/\ unlock_msg' = [unlock_msg EXCEPT![n] = TRUE]

RecvUnlock(n) ==
/\ unlock_msg[n]
/\ unlock_msg' = [k \in Node |-> (unlock_msg[k] /\ k /= n)]

Next ==
\/ (\E n \in Node : Unlock(n))
\/ (\E n \in Node : RecvUnlock(n))

Init ==
/\ unlock_msg = [n \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (unlock_msg \in [Node -> BOOLEAN])
=============================================================================
