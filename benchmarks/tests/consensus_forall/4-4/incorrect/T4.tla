--------------------------- MODULE T4 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES voting_quorum, voted, votes

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<voted,votes,voting_quorum>>

SendVote(src,dst) ==
/\ ~(voted[src])
/\ voted' = [voted EXCEPT![src] = TRUE]
/\ UNCHANGED <<votes,voting_quorum>>

RecvVote(i,sender) ==
/\ votes' = (votes \cup {<<i,sender>>})
/\ UNCHANGED <<voted,voting_quorum>>

ChooseVotingQuorum(i) ==
\E Q \in Quorum :
/\ (\A v \in Q : (<<i,v>> \in votes))
/\ voting_quorum' = Q
/\ UNCHANGED <<votes,voted>>

BecomeLeader(i) ==
/\ voting_quorum /= {}
/\ (\A v \in voting_quorum : (<<i,v>> \in votes))
/\ UNCHANGED <<voted,votes,voting_quorum>>

Init ==
/\ voted = [s \in Node |-> FALSE]
/\ votes = {}
/\ (voting_quorum \in Quorum)

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
\/ SendVoteAction
\/ RecvVoteAction
\/ ChooseVotingQuorumAction
\/ BecomeLeaderAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (voted \in [Node -> BOOLEAN])
/\ (votes \in SUBSET((Node \X Node)))
/\ (voting_quorum \in Quorum)
=============================================================================
