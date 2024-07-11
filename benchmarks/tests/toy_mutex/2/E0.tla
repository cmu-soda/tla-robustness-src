--------------------------- MODULE E0 ---------------------------
EXTENDS Naturals

VARIABLES isLocked, globalVar

Processes == {"p","q"}

Max == 1

vars == <<isLocked,globalVar>>

Init ==
/\ isLocked = FALSE
/\ globalVar = 0

EnterCS(proc) ==
/\ isLocked = FALSE
/\ isLocked' = TRUE
/\ UNCHANGED <<globalVar>>

InCS(proc) ==
/\ globalVar < Max
/\ globalVar' = (globalVar + 1)
/\ UNCHANGED <<isLocked>>

ExitCS(proc) ==
/\ isLocked' = FALSE
/\ UNCHANGED <<globalVar>>

Next ==
\E proc \in Processes :
\/ EnterCS(proc)
\/ InCS(proc)
\/ ExitCS(proc)

Spec == (Init /\ [][Next]_vars)
=============================================================================
