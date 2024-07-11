--------------------------- MODULE D0 ---------------------------


VARIABLES holds_lock, unlock_msg

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<unlock_msg,holds_lock>>

RecvGrant(n) ==
/\ holds_lock' = [holds_lock EXCEPT![n] = TRUE]
/\ UNCHANGED <<unlock_msg>>

Unlock(n) ==
/\ holds_lock[n]
/\ holds_lock' = [k \in Node |-> (holds_lock[k] /\ k /= n)]
/\ unlock_msg' = [unlock_msg EXCEPT![n] = TRUE]

RecvUnlock(n) ==
/\ unlock_msg[n]
/\ unlock_msg' = [k \in Node |-> (unlock_msg[k] /\ k /= n)]
/\ UNCHANGED <<holds_lock>>

Next ==
\/ (\E n \in Node : RecvGrant(n))
\/ (\E n \in Node : Unlock(n))
\/ (\E n \in Node : RecvUnlock(n))

Init ==
/\ unlock_msg = [n \in Node |-> FALSE]
/\ holds_lock = [n \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (unlock_msg \in [Node -> BOOLEAN])
/\ (holds_lock \in [Node -> BOOLEAN])

Mutex == (\A x,y \in Node : ((holds_lock[x] /\ holds_lock[y]) => x = y))
=============================================================================
