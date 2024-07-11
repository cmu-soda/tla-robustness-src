--------------------------- MODULE D3 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES vote_msg, voted

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<voted,vote_msg>>

SendVote(src,dst) ==
/\ ~(voted[src])
/\ vote_msg' = (vote_msg \cup {<<src,dst>>})
/\ voted' = [voted EXCEPT![src] = TRUE]

RecvVote(i,sender) ==
/\ (<<sender,i>> \in vote_msg)
/\ UNCHANGED <<vote_msg,voted>>

Init ==
/\ voted = [s \in Node |-> FALSE]
/\ vote_msg = {}

SendVoteAction ==
\E i,j \in Node :
SendVote(i,j)

RecvVoteAction ==
\E i,j \in Node :
RecvVote(i,j)

Next ==
\/ SendVoteAction
\/ RecvVoteAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (voted \in [Node -> BOOLEAN])
/\ (vote_msg \in SUBSET((Node \X Node)))
=============================================================================
