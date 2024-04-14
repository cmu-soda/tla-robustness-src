---- MODULE toy_consensus ----
\* benchmark: ex-toy-consensus

EXTENDS TLC, FiniteSets, Naturals

Node == {"n1","n2","n3","n4","n5","n6","n7","n8"}
Value == {"v1","v2","v3"}
Nil == "nil"

VARIABLE vote
VARIABLE decision

vars == <<vote,decision>>

Quorums == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

ChosenAt(v, Q) == \A m \in Q : vote[m] = v

\* Node i casts vote for value 'v'.
CastVote(i, v) ==
    /\ vote[i] = Nil
    /\ vote' = [vote EXCEPT ![i] = v]
    /\ UNCHANGED decision
    
\* Decide on value 'v' with quorum 'Q'.
Decide(v, Q) ==
    /\ ChosenAt(v, Q)
    /\ decision' = decision \cup {v}
    /\ UNCHANGED vote

Init == 
    /\ vote = [n \in Node |-> Nil]
    /\ decision = {}

Next == 
    \/ \E i \in Node, v \in Value : CastVote(i, v)
    \/ \E v \in Value, Q \in Quorums : Decide(v, Q)

Spec == Init /\ [][Next]_vars

TypeOK == 
    /\ vote \in [Node -> Value \cup {Nil}]
    /\ decision \in SUBSET Value

\* At most one value is decided upon.
Inv == \A vi, vj \in decision : vi = vj

====
