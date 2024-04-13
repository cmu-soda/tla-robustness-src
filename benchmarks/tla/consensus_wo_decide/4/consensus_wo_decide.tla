---- MODULE consensus_wo_decide ----
\* benchmark: pyv-consensus-wo-decide

EXTENDS TLC, FiniteSets, Naturals

Node == {"n1","n2","n3","n4"}
Quorums == { S \in SUBSET Node : Cardinality(S)*2 > Cardinality(Node) }

VARIABLE vote_request_msg
VARIABLE voted
VARIABLE vote_msg
VARIABLE votes
VARIABLE leader
VARIABLE voting_quorum

vars == <<vote_request_msg, voted, vote_msg, votes, leader, voting_quorum>>

SendRequestVote(i,j) == 
    /\ vote_request_msg' = [vote_request_msg EXCEPT ![<<i,j>>] = TRUE]
    /\ UNCHANGED <<voted, vote_msg, votes, leader, voting_quorum>>

SendVote(src,dst)==
    /\ ~voted[src]
    /\ vote_request_msg[<<dst,src>>]
    /\ vote_msg' = [vote_msg EXCEPT ![<<src,dst>>] = TRUE]
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    /\ UNCHANGED <<vote_request_msg, votes, leader, voting_quorum>>

RecvVote(i,sender)==
    /\ vote_msg[<<sender,i>>]
    /\ votes' = [votes EXCEPT ![<<i,sender>>] = TRUE]
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, leader, voting_quorum>>

ChooseVotingQuorum(i,Q) ==
    /\ \A v \in Q : votes[<<i,v>>]
    /\ voting_quorum' = Q
    /\ UNCHANGED <<vote_request_msg, vote_msg, votes, voted, leader>>

BecomeLeader(i) == 
    /\ voting_quorum # {}
    /\ \A v \in voting_quorum : votes[<<i,v>>]
    /\ leader' = [leader EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, votes, voting_quorum>>

Init == 
    /\ vote_request_msg = [s \in Node \X Node |-> FALSE]
    /\ voted = [s \in Node |-> FALSE]
    /\ vote_msg = [s \in Node \X Node |-> FALSE]
    /\ votes = [s \in Node \X Node |-> FALSE]
    /\ leader = [s \in Node |-> FALSE]
    /\ voting_quorum \in Quorums

Next == 
    \/ \E i,j \in Node : SendRequestVote(i,j)
    \/ \E i,j \in Node : SendVote(i,j)
    \/ \E i,j \in Node : RecvVote(i,j)
    \/ \E i \in Node : \E Q \in Quorums : ChooseVotingQuorum(i,Q)
    \/ \E i \in Node : BecomeLeader(i)

TypeOK == 
    /\ vote_request_msg \in [Node \X Node -> BOOLEAN]
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in [Node \X Node -> BOOLEAN]
    /\ votes \in [Node \X Node -> BOOLEAN]
    /\ leader \in [Node -> BOOLEAN]
    /\ voting_quorum \in Quorums

Spec == Init /\ [][Next]_vars

Safety == \A i,j \in Node : (leader[i] /\ leader[j]) => (i = j)

====
