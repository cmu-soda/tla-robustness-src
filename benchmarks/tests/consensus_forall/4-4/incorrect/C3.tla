--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES leader

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<leader>>

BecomeLeader(i) ==
/\ leader' = [leader EXCEPT![i] = TRUE]

Decide(i,v) ==
/\ leader[i]
/\ UNCHANGED <<leader>>

Init ==
/\ leader = [s \in Node |-> FALSE]

BecomeLeaderAction ==
\E i \in Node :
BecomeLeader(i)

DecideAction ==
\E i \in Node, v \in Value :
Decide(i,v)

Next ==
\/ BecomeLeaderAction
\/ DecideAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (leader \in [Node -> BOOLEAN])
=============================================================================
