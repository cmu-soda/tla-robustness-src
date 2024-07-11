---- MODULE firewall ----
\* benchmark: pyv-firewall

EXTENDS TLC

Node == {"n1","n2","n3","n4","n5"}

VARIABLE internal
VARIABLE sent
VARIABLE allowed_in

vars == <<internal,sent,allowed_in>>

SendFromInternal(src, dest) == 
    /\ internal[src]
    /\ ~internal[dest]
    /\ sent' = [sent EXCEPT ![src] = @ \cup {dest}]
    /\ allowed_in' = allowed_in \cup {dest}
    /\ UNCHANGED internal

SendToInternal(src, dest) == 
    /\ ~internal[src]
    /\ internal[dest]
    /\ src \in allowed_in
    /\ sent' = [sent EXCEPT ![src] = @ \cup {dest}]
    /\ UNCHANGED <<internal, allowed_in>>

Init == 
    /\ internal \in [Node -> BOOLEAN]
    /\ sent = [n \in Node |-> {}]
    /\ allowed_in = {}

Next == 
    \/ \E s,t \in Node : SendFromInternal(s,t)
    \/ \E s,t \in Node : SendToInternal(s,t)

Spec == Init /\ [][Next]_vars

Inv == 
    \A s,d \in Node:
        (d \in sent[s] /\ internal[d]) => 
        (\E i \in Node : internal[i] /\ s \in sent[i])

TypeOK ==
    /\ internal \in [Node -> BOOLEAN]
    /\ sent \in [Node -> SUBSET Node]
    /\ allowed_in \in SUBSET Node

====
