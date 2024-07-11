--------------------------- MODULE C3 ---------------------------


VARIABLES grant_msg

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<grant_msg>>

RecvLock(n) ==
/\ grant_msg' = [grant_msg EXCEPT![n] = TRUE]

RecvGrant(n) ==
/\ grant_msg[n]
/\ grant_msg' = [k \in Node |-> (grant_msg[k] /\ k /= n)]

Next ==
\/ (\E n \in Node : RecvLock(n))
\/ (\E n \in Node : RecvGrant(n))

Init ==
/\ grant_msg = [n \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (grant_msg \in [Node -> BOOLEAN])
=============================================================================
