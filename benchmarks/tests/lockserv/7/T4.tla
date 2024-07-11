--------------------------- MODULE T4 ---------------------------


VARIABLES lock_msg

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<lock_msg>>

SendLock(n) ==
/\ lock_msg' = [lock_msg EXCEPT![n] = TRUE]

RecvLock(n) ==
/\ lock_msg[n]
/\ lock_msg' = [k \in Node |-> (lock_msg[k] /\ k /= n)]

Next ==
\/ (\E n \in Node : SendLock(n))
\/ (\E n \in Node : RecvLock(n))

Init ==
/\ lock_msg = [n \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (lock_msg \in [Node -> BOOLEAN])
=============================================================================
