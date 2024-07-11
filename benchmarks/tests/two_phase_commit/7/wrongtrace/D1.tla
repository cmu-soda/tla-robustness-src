--------------------------- MODULE D1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES go_abort

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<go_abort>>

Go1 ==
/\ (\A n \in Node : (n \notin go_abort))
/\ UNCHANGED <<go_abort>>

Go2 ==
/\ (\A n \in Node : (n \notin go_abort))
/\ go_abort' = Node

Abort(n) ==
/\ (n \in go_abort)
/\ UNCHANGED <<go_abort>>

Next ==
\/ Go1
\/ Go2
\/ Abort("n2")

Init ==
/\ go_abort = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (go_abort \in SUBSET(Node))
=============================================================================
