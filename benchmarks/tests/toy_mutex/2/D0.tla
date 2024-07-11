--------------------------- MODULE D0 ---------------------------
EXTENDS Naturals

VARIABLES criticalSection

Processes == {"p","q"}

Max == 1

vars == <<criticalSection>>

Init ==
/\ criticalSection = {}

EnterCS(proc) ==
/\ criticalSection' = (criticalSection \cup {proc})

InCS(proc) ==
/\ (proc \in criticalSection)
/\ UNCHANGED <<criticalSection>>

ExitCS(proc) ==
/\ (proc \in criticalSection)
/\ criticalSection' = (criticalSection \ {proc})

Next ==
\E proc \in Processes :
\/ EnterCS(proc)
\/ InCS(proc)
\/ ExitCS(proc)

Spec == (Init /\ [][Next]_vars)

Mutex == (\A p,q \in Processes : (((p \in criticalSection) /\ (q \in criticalSection)) => p = q))
=============================================================================
