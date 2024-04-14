---- MODULE naive_consensus ----
\* benchmark: ex-naive-consensus

EXTENDS FiniteSets, Naturals

Node == {"n1","n2","n3","n4"}
Value == {"v1","v2","v3","v4"}

Quorum == { S \in SUBSET Node : Cardinality(S)*2 > Cardinality(Node) }

VARIABLE vote
VARIABLE decide
VARIABLE decision

vars == <<vote,decide,decision>>

VotedFor(v) == \E Q \in Quorum : <<Q,v>> \in decide

CastVote(n, v) ==
    /\ \A x \in Value : <<n,x>> \notin vote
    /\ vote' = vote \cup {<<n,v>>}
    /\ UNCHANGED <<decide, decision>>

CollectVotes(Q, v) ==
    /\ \A n \in Q : <<n,v>> \in vote
    /\ decide' = decide \cup {<<Q,v>>}
    /\ UNCHANGED <<vote, decision>>

LearnValue(Q, v) ==
    /\ <<Q,v>> \in decide
    /\ decision' = decision \cup {v}
    /\ UNCHANGED <<vote, decide>>

Init == 
    /\ vote = {}
    /\ decide = {}
    /\ decision = {}

Next == 
    \/ \E n \in Node, v \in Value : CastVote(n,v)
    \/ \E Q \in Quorum, v \in Value : CollectVotes(Q,v)
    \/ \E Q \in Quorum, v \in Value : LearnValue(Q,v)

Spec == Init /\ [][Next]_vars

TypeOK == 
    /\ vote \in SUBSET (Node \X Value)
    /\ decide \in SUBSET (Quorum \X Value)
    /\ decision \in SUBSET Value

Safety == \A v1,v2 \in Value : (v1 \in decision /\ v2 \in decision) => (v1=v2)

====
