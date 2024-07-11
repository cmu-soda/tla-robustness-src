--------------------------- MODULE D1 ---------------------------


VARIABLES server_holds_lock, grant_msg

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<grant_msg,server_holds_lock>>

RecvLock(n) ==
/\ server_holds_lock
/\ server_holds_lock' = FALSE
/\ grant_msg' = [grant_msg EXCEPT![n] = TRUE]

RecvGrant(n) ==
/\ grant_msg[n]
/\ grant_msg' = [k \in Node |-> (grant_msg[k] /\ k /= n)]
/\ UNCHANGED <<server_holds_lock>>

RecvUnlock(n) ==
/\ server_holds_lock' = TRUE
/\ UNCHANGED <<grant_msg>>

Next ==
\/ (\E n \in Node : RecvLock(n))
\/ (\E n \in Node : RecvGrant(n))
\/ (\E n \in Node : RecvUnlock(n))

Init ==
/\ grant_msg = [n \in Node |-> FALSE]
/\ server_holds_lock = TRUE

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (grant_msg \in [Node -> BOOLEAN])
/\ (server_holds_lock \in BOOLEAN)
=============================================================================
