--------------------------- MODULE C2 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES alive, vote_no

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<vote_no,alive>>

Vote1(n) ==
/\ (n \in alive)
/\ (n \notin vote_no)
/\ UNCHANGED <<vote_no,alive>>

Vote2(n) ==
/\ (n \in alive)
/\ vote_no' = (vote_no \cup {n})
/\ UNCHANGED <<alive>>

Fail(n) ==
/\ (n \in alive)
/\ alive' = (alive \ {n})
/\ UNCHANGED <<vote_no>>

Go2 ==
/\ (\E n \in Node : ((n \in vote_no) \/ (n \notin alive)))
/\ UNCHANGED <<vote_no,alive>>

Commit(n) ==
/\ (n \in alive)
/\ UNCHANGED <<vote_no,alive>>

Abort(n) ==
/\ (n \in alive)
/\ UNCHANGED <<vote_no,alive>>

Next ==
\/ Vote1("n1")
\/ Vote1("n2")
\/ Go2
\/ Commit("n1")
\/ Abort("n2")

Init ==
/\ vote_no = {}
/\ alive = Node

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (vote_no \in SUBSET(Node))
/\ (alive \in SUBSET(Node))
=============================================================================
