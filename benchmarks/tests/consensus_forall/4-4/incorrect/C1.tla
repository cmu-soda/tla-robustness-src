--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES decided

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<decided>>

Decide(i,v) ==
/\ (\A vx \in Value : (<<i,vx>> \notin decided))
/\ decided' = (decided \cup {<<i,v>>})

Init ==
/\ decided = {}

DecideAction ==
\E i \in Node, v \in Value :
Decide(i,v)

Next ==
\/ DecideAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (decided \in SUBSET((Node \X Value)))

Safety == (\A n1,n2 \in Node : (\A v1,v2 \in Value : (((<<n1,v1>> \in decided) /\ (<<n2,v2>> \in decided)) => v1 = v2)))
=============================================================================
