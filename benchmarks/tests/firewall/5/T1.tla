--------------------------- MODULE T1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES allowed_in

Node == {"n1","n2","n3","n4","n5"}

vars == <<allowed_in>>

SendFromInternal(src,dest) ==
/\ allowed_in' = (allowed_in \cup {dest})

SendToInternal(src,dest) ==
/\ (src \in allowed_in)
/\ UNCHANGED <<allowed_in>>

Init ==
/\ allowed_in = {}

Next ==
\/ (\E s,t \in Node : SendFromInternal(s,t))
\/ (\E s,t \in Node : SendToInternal(s,t))

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (allowed_in \in SUBSET(Node))
=============================================================================
