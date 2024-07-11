--------------------------- MODULE D2 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES voting_quorum, votes

Node == {"n1","n2","n3","n4"}

Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET(Node) : (Cardinality(S) * 2) > Cardinality(Node) }

vars == <<votes,voting_quorum>>

RecvVote(i,sender) ==
/\ votes' = (votes \cup {<<i,sender>>})
/\ UNCHANGED <<voting_quorum>>

ChooseVotingQuorum(i) ==
\E Q \in Quorum :
/\ (\A v \in Q : (<<i,v>> \in votes))
/\ voting_quorum' = Q
/\ UNCHANGED <<votes>>

BecomeLeader(i) ==
/\ voting_quorum /= {}
/\ (\A v \in voting_quorum : (<<i,v>> \in votes))
/\ UNCHANGED <<votes,voting_quorum>>

Init ==
/\ votes = {}
/\ (voting_quorum \in Quorum)

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
\/ RecvVoteAction
\/ ChooseVotingQuorumAction
\/ BecomeLeaderAction

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (votes \in SUBSET((Node \X Node)))
/\ (voting_quorum \in Quorum)
=============================================================================
