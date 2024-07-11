--------------------------- MODULE C2 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES vote_msg

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<vote_msg>>

SendVote(src,dst) ==
/\ vote_msg' = (vote_msg \cup {<<src,dst>>})

RecvVote(i,sender) ==
/\ (<<sender,i>> \in vote_msg)
/\ UNCHANGED <<vote_msg>>

Init ==
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
/\ (vote_msg \in SUBSET((Node \X Node)))
=============================================================================
