------------------------------ MODULE ToyMutex ------------------------------

EXTENDS Naturals

Processes == {"p","q"}
Max == 1

ASSUME Max \in Nat

VARIABLES isLocked, criticalSection, globalVar

vars == <<isLocked, criticalSection, globalVar>>


Init ==
    /\ isLocked = FALSE
    /\ criticalSection = {}
    /\ globalVar = 0

EnterCS(proc) ==
    /\ isLocked = FALSE
    /\ isLocked' = TRUE
    /\ criticalSection' = criticalSection \cup {proc}
    /\ UNCHANGED <<globalVar>>

InCS(proc) ==
    /\ proc \in criticalSection
    /\ globalVar < Max
    /\ globalVar' = globalVar + 1
    /\ UNCHANGED <<isLocked, criticalSection>>

ExitCS(proc) ==
    /\ proc \in criticalSection
    /\ criticalSection' = criticalSection \ {proc}
    /\ isLocked' = FALSE
    /\ UNCHANGED <<globalVar>>

Next ==
    \E proc \in Processes :
        \/ EnterCS(proc)
        \/ InCS(proc)
        \/ ExitCS(proc)

Spec == Init /\ [][Next]_vars

Mutex == \A p,q \in Processes : (p \in criticalSection /\ q \in criticalSection) => (p = q)

=============================================================================
