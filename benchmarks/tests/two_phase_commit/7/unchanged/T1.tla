--------------------------- MODULE T1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES alive, go_commit, go_abort, vote_no

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<vote_no,alive,go_commit,go_abort>>

Vote1(n) ==
/\ (n \in alive)
/\ (n \notin vote_no)
/\ UNCHANGED <<vote_no,alive,go_commit,go_abort>>

Vote2(n) ==
/\ (n \in alive)
/\ vote_no' = (vote_no \cup {n})
/\ UNCHANGED <<alive,go_commit,go_abort>>

Fail(n) ==
/\ (n \in alive)
/\ alive' = (alive \ {n})
/\ UNCHANGED <<vote_no,go_commit,go_abort>>

Go1 ==
/\ (\A n \in Node : (n \notin go_commit))
/\ (\A n \in Node : (n \notin go_abort))
/\ go_commit' = Node
/\ UNCHANGED <<vote_no,alive,go_abort>>

Go2 ==
/\ (\A n \in Node : (n \notin go_commit))
/\ (\A n \in Node : (n \notin go_abort))
/\ (\E n \in Node : ((n \in vote_no) \/ (n \notin alive)))
/\ go_abort' = Node
/\ UNCHANGED <<vote_no,alive,go_commit>>

Commit(n) ==
/\ (n \in alive)
/\ (n \in go_commit)
/\ UNCHANGED <<vote_no,alive,go_commit,go_abort>>

Abort(n) ==
/\ (n \in alive)
/\ (n \in go_abort)
/\ UNCHANGED <<vote_no,alive,go_commit,go_abort>>

Next ==
\/ Vote1("n1")
\/ Vote1("n2")
\/ Go1
\/ Go2
\/ Commit("n1")
\/ Abort("n2")

Init ==
/\ vote_no = {}
/\ alive = Node
/\ go_commit = {}
/\ go_abort = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (vote_no \in SUBSET(Node))
/\ (alive \in SUBSET(Node))
/\ (go_commit \in SUBSET(Node))
/\ (go_abort \in SUBSET(Node))
=============================================================================
