--------------------------- MODULE E1 ---------------------------
EXTENDS Naturals

VARIABLES isLocked

Processes == {"p","q"}

Max == 1

vars == <<isLocked>>

Init ==
/\ isLocked = FALSE

EnterCS(proc) ==
/\ isLocked = FALSE
/\ isLocked' = TRUE

ExitCS(proc) ==
/\ isLocked' = FALSE

Next ==
\E proc \in Processes :
\/ EnterCS(proc)
\/ ExitCS(proc)

Spec == (Init /\ [][Next]_vars)
=============================================================================
