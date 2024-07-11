--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES internal, sent

Node == {"n1","n2","n3","n4","n5"}

vars == <<internal,sent>>

SendFromInternal(src,dest) ==
/\ internal[src]
/\ ~(internal[dest])
/\ sent' = [sent EXCEPT![src] = (@ \cup {dest})]
/\ UNCHANGED internal

SendToInternal(src,dest) ==
/\ ~(internal[src])
/\ internal[dest]
/\ sent' = [sent EXCEPT![src] = (@ \cup {dest})]
/\ UNCHANGED <<internal>>

Init ==
/\ (internal \in [Node -> BOOLEAN])
/\ sent = [n \in Node |-> {}]

Next ==
\/ (\E s,t \in Node : SendFromInternal(s,t))
\/ (\E s,t \in Node : SendToInternal(s,t))

Spec == (Init /\ [][Next]_vars)

Inv == (\A s,d \in Node : (((d \in sent[s]) /\ internal[d]) => (\E i \in Node : (internal[i] /\ (s \in sent[i])))))

TypeOK ==
/\ (internal \in [Node -> BOOLEAN])
/\ (sent \in [Node -> SUBSET(Node)])
=============================================================================
