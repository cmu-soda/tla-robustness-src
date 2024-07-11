--------------------------- MODULE D1 ---------------------------
EXTENDS Naturals

VARIABLES globalVar

Processes == {"p","q"}

Max == 1

vars == <<globalVar>>

Init ==
/\ globalVar = 0

InCS(proc) ==
/\ globalVar < Max
/\ globalVar' = (globalVar + 1)

Next ==
\E proc \in Processes :
\/ InCS(proc)

Spec == (Init /\ [][Next]_vars)
=============================================================================
