---- MODULE majorityset_leader_election ----
\* benchmark: ex-majorityset-leader-election

EXTENDS TLC, Naturals, FiniteSets

Node == {"n1","n2","n3","n4","n5"}

VARIABLE vote
VARIABLE leader
VARIABLE voters

vars == <<vote,leader,voters>>

\* The set of node majorities.
Majority == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

DidNotVote(n) == vote[n] = {}

Voting(n1,n2) ==
    /\ DidNotVote(n1)
    /\ vote' = [vote EXCEPT ![n1] = @ \cup {n2}]
    /\ UNCHANGED <<leader,voters>>

ReceiveVote(voter,n,vs) ==
    /\ n \in vote[voter]
    /\ voters[n] = vs
    /\ voter \notin vs
    /\ voters' = [voters EXCEPT ![n] = vs \cup {voter}]
    /\ UNCHANGED <<vote,leader>>

BecomeLeader(n, vs) ==
    /\ voters[n] = vs
    /\ vs \in Majority
    /\ leader' = leader \cup {n}
    /\ UNCHANGED <<vote,voters>>

Next ==
    \/ \E n1,n2 \in Node : Voting(n1,n2)
    \/ \E voter,n \in Node, vs \in SUBSET Node : ReceiveVote(voter,n,vs)
    \/ \E n \in Node, vs \in SUBSET Node : BecomeLeader(n, vs)

EmptySet == {}

Init ==
    /\ vote = [n \in Node |-> {}]
    /\ leader = {}
    /\ voters = [n \in Node |-> {}]

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ vote \in [Node -> SUBSET Node]
    /\ leader \in SUBSET Node
    /\ voters \in [Node -> SUBSET Node]

Safety == \A x,y \in Node : (x \in leader) /\ (y \in leader) => (x = y)

====
