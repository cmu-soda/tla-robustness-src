--------------------------- MODULE C1 ---------------------------


VARIABLES holds_lock

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<holds_lock>>

RecvGrant(n) ==
/\ holds_lock' = [holds_lock EXCEPT![n] = TRUE]

Unlock(n) ==
/\ holds_lock[n]
/\ holds_lock' = [k \in Node |-> (holds_lock[k] /\ k /= n)]

Next ==
\/ (\E n \in Node : RecvGrant(n))
\/ (\E n \in Node : Unlock(n))

Init ==
/\ holds_lock = [n \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (holds_lock \in [Node -> BOOLEAN])

Mutex == (\A x,y \in Node : ((holds_lock[x] /\ holds_lock[y]) => x = y))
=============================================================================
