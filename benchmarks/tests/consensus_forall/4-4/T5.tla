--------------------------- MODULE T5 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES voted

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<voted>>

SendVote(src,dst) ==
/\ ~(voted[src])
/\ voted' = [voted EXCEPT![src] = TRUE]

Init ==
/\ voted = [s \in Node |-> FALSE]

SendVoteAction ==
\E i,j \in Node :
SendVote(i,j)

Next ==
\/ SendVoteAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (voted \in [Node -> BOOLEAN])
=============================================================================
