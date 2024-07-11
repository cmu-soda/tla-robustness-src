--------------------------- MODULE E1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES vote_msg, vote_request_msg, voting_quorum, voted, votes

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<vote_request_msg,voted,vote_msg,votes,voting_quorum>>

SendRequestVote(i,j) ==
/\ vote_request_msg' = (vote_request_msg \cup {<<i,j>>})
/\ UNCHANGED <<voted,vote_msg,votes,voting_quorum>>

SendVote(src,dst) ==
/\ ~(voted[src])
/\ (<<dst,src>> \in vote_request_msg)
/\ vote_msg' = (vote_msg \cup {<<src,dst>>})
/\ voted' = [voted EXCEPT![src] = TRUE]
/\ UNCHANGED <<vote_request_msg,votes,voting_quorum>>

RecvVote(i,sender) ==
/\ (<<sender,i>> \in vote_msg)
/\ votes' = (votes \cup {<<i,sender>>})
/\ UNCHANGED <<vote_request_msg,vote_msg,voted,voting_quorum>>

ChooseVotingQuorum(i) ==
\E Q \in Quorum :
/\ (\A v \in Q : (<<i,v>> \in votes))
/\ voting_quorum' = Q
/\ UNCHANGED <<vote_request_msg,vote_msg,votes,voted>>

BecomeLeader(i) ==
/\ voting_quorum /= {}
/\ (\A v \in voting_quorum : (<<i,v>> \in votes))
/\ UNCHANGED <<vote_request_msg,vote_msg,voted,votes,voting_quorum>>

Init ==
/\ vote_request_msg = {}
/\ voted = [s \in Node |-> FALSE]
/\ vote_msg = {}
/\ votes = {}
/\ (voting_quorum \in Quorum)

SendRequestVoteAction ==
\E i,j \in Node :
SendRequestVote(i,j)

SendVoteAction ==
\E i,j \in Node :
SendVote(i,j)

RecvVoteAction ==
\E i,j \in Node :
RecvVote(i,j)

ChooseVotingQuorumAction ==
\E i \in Node :
ChooseVotingQuorum(i)

BecomeLeaderAction ==
\E i \in Node :
BecomeLeader(i)

Next ==
\/ SendRequestVoteAction
\/ SendVoteAction
\/ RecvVoteAction
\/ ChooseVotingQuorumAction
\/ BecomeLeaderAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (vote_request_msg \in SUBSET((Node \X Node)))
/\ (voted \in [Node -> BOOLEAN])
/\ (vote_msg \in SUBSET((Node \X Node)))
/\ (votes \in SUBSET((Node \X Node)))
/\ (voting_quorum \in Quorum)
=============================================================================
