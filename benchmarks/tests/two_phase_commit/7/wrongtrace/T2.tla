--------------------------- MODULE T2 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES go_commit, go_abort

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<go_commit,go_abort>>

Go1 ==
/\ (\A n \in Node : (n \notin go_commit))
/\ (\A n \in Node : (n \notin go_abort))
/\ go_commit' = Node
/\ UNCHANGED <<go_abort>>

Go2 ==
/\ (\A n \in Node : (n \notin go_commit))
/\ (\A n \in Node : (n \notin go_abort))
/\ go_abort' = Node
/\ UNCHANGED <<go_commit>>

Commit(n) ==
/\ (n \in go_commit)
/\ UNCHANGED <<go_commit,go_abort>>

Abort(n) ==
/\ (n \in go_abort)
/\ UNCHANGED <<go_commit,go_abort>>

Next ==
\/ Go1
\/ Go2
\/ Commit("n1")
\/ Abort("n2")

Init ==
/\ go_commit = {}
/\ go_abort = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (go_commit \in SUBSET(Node))
/\ (go_abort \in SUBSET(Node))
=============================================================================
