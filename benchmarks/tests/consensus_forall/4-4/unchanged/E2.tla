--------------------------- MODULE E2 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES vote_msg, vote_request_msg, voted

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<vote_request_msg,voted,vote_msg>>

SendRequestVote(i,j) ==
/\ vote_request_msg' = (vote_request_msg \cup {<<i,j>>})
/\ UNCHANGED <<voted,vote_msg>>

SendVote(src,dst) ==
/\ ~(voted[src])
/\ (<<dst,src>> \in vote_request_msg)
/\ vote_msg' = (vote_msg \cup {<<src,dst>>})
/\ voted' = [voted EXCEPT![src] = TRUE]
/\ UNCHANGED <<vote_request_msg>>

RecvVote(i,sender) ==
/\ (<<sender,i>> \in vote_msg)
/\ UNCHANGED <<vote_request_msg,vote_msg,voted>>

Init ==
/\ vote_request_msg = {}
/\ voted = [s \in Node |-> FALSE]
/\ vote_msg = {}

SendRequestVoteAction ==
\E i,j \in Node :
SendRequestVote(i,j)

SendVoteAction ==
\E i,j \in Node :
SendVote(i,j)

RecvVoteAction ==
\E i,j \in Node :
RecvVote(i,j)

Next ==
\/ SendRequestVoteAction
\/ SendVoteAction
\/ RecvVoteAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (vote_request_msg \in SUBSET((Node \X Node)))
/\ (voted \in [Node -> BOOLEAN])
/\ (vote_msg \in SUBSET((Node \X Node)))
=============================================================================
