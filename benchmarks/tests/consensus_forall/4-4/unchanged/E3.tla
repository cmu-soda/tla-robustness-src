--------------------------- MODULE E3 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES vote_request_msg

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<vote_request_msg>>

SendRequestVote(i,j) ==
/\ vote_request_msg' = (vote_request_msg \cup {<<i,j>>})

SendVote(src,dst) ==
/\ (<<dst,src>> \in vote_request_msg)
/\ UNCHANGED <<vote_request_msg>>

Init ==
/\ vote_request_msg = {}

SendRequestVoteAction ==
\E i,j \in Node :
SendRequestVote(i,j)

SendVoteAction ==
\E i,j \in Node :
SendVote(i,j)

Next ==
\/ SendRequestVoteAction
\/ SendVoteAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (vote_request_msg \in SUBSET((Node \X Node)))
=============================================================================
