--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES go_commit

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<go_commit>>

Go1 ==
/\ (\A n \in Node : (n \notin go_commit))
/\ go_commit' = Node

Go2 ==
/\ (\A n \in Node : (n \notin go_commit))
/\ UNCHANGED <<go_commit>>

Commit(n) ==
/\ (n \in go_commit)
/\ UNCHANGED <<go_commit>>

Next ==
\/ Go1
\/ Go2
\/ Commit("n1")

Init ==
/\ go_commit = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (go_commit \in SUBSET(Node))
=============================================================================
