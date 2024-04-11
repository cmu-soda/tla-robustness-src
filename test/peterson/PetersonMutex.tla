---- MODULE PetersonMutex ----
EXTENDS TLC, Naturals, FiniteSets

ProcSet == {0,1}

(* variable order:
flag0
flag1
pc0_CS
pc0_a1
pc0_a2
pc0_a3
pc0_a4
pc0_a5
pc1_CS
pc1_a1
pc1_a2
pc1_a3
pc1_a4
pc1_a5
turn
*)

VARIABLE turn, flag0, flag1, pc0_a1, pc0_a2, pc0_a3, pc0_a4, pc0_CS, pc0_a5, pc1_a1, pc1_a2, pc1_a3, pc1_a4, pc1_CS, pc1_a5

vars == <<turn, flag0, flag1, pc0_a1, pc0_a2, pc0_a3, pc0_a4, pc0_CS, pc0_a5, pc1_a1, pc1_a2, pc1_a3, pc1_a4, pc1_CS, pc1_a5>>

Init == 
    /\ turn \in ProcSet
    /\ flag0 = FALSE
    /\ flag1 = FALSE
    /\ pc0_a1 = TRUE
    /\ pc0_a2 = FALSE
    /\ pc0_a3 = FALSE
    /\ pc0_a4 = FALSE
    /\ pc0_CS = FALSE
    /\ pc0_a5 = FALSE
    /\ pc1_a1 = TRUE
    /\ pc1_a2 = FALSE
    /\ pc1_a3 = FALSE
    /\ pc1_a4 = FALSE
    /\ pc1_CS = FALSE
    /\ pc1_a5 = FALSE

a1(self) ==
    /\ IF self = 0
       THEN
        /\ pc0_a1
        /\ pc0_a1' = FALSE
        /\ pc0_a2' = TRUE
        /\ pc1_a1' = pc1_a1
        /\ pc1_a2' = pc1_a2
       ELSE
        /\ pc1_a1
        /\ pc1_a1' = FALSE
        /\ pc1_a2' = TRUE
        /\ pc0_a1' = pc0_a1
        /\ pc0_a2' = pc0_a2
    /\ UNCHANGED <<turn, flag0, flag1, pc0_a3, pc0_a4, pc0_CS, pc0_a5, pc1_a3, pc1_a4, pc1_CS, pc1_a5>>

\* A process sets its own flag to TRUE.
a2(self) ==
    /\ IF self = 0
       THEN
        /\ pc0_a2
        /\ flag0' = TRUE
        /\ pc0_a2' = FALSE
        /\ pc0_a3' = TRUE
        /\ flag1' = flag1
        /\ pc1_a2' = pc1_a2
        /\ pc1_a3' = pc1_a3
       ELSE
        /\ pc1_a2
        /\ flag1' = TRUE
        /\ pc1_a2' = FALSE
        /\ pc1_a3' = TRUE
        /\ flag0' = flag0
        /\ pc0_a2' = pc0_a2
        /\ pc0_a3' = pc0_a3
    /\ UNCHANGED <<turn, pc0_a1, pc0_a4, pc0_CS, pc0_a5, pc1_a1, pc1_a4, pc1_CS, pc1_a5>>

\* A process updates 'turn'.
a3(self, other) ==
    /\ self # other
    /\ IF self = 0
       THEN
        /\ pc0_a3
        /\ turn' = other
        /\ pc0_a3' = FALSE
        /\ pc0_a4' = TRUE
        /\ pc1_a3' = pc1_a3
        /\ pc1_a4' = pc1_a4
       ELSE
        /\ pc1_a3
        /\ turn' = other
        /\ pc1_a3' = FALSE
        /\ pc1_a4' = TRUE
        /\ pc0_a3' = pc0_a3
        /\ pc0_a4' = pc0_a4
    /\ UNCHANGED <<flag0, flag1, pc0_a1, pc0_a2, pc0_CS, pc0_a5, pc1_a1, pc1_a2, pc1_CS, pc1_a5>>

\* A process enters the critical section.
a4(self, other) == 
    /\ self # other
    /\ IF self = 0
       THEN
        /\ pc0_a4
        /\ ~flag1 \/ turn = self
        /\ pc0_a4' = FALSE
        /\ pc0_CS' = TRUE
        /\ pc1_a4' = pc1_a4
        /\ pc1_CS' = pc1_CS
       ELSE
        /\ pc1_a4
        /\ ~flag0 \/ turn = self
        /\ pc1_a4' = FALSE
        /\ pc1_CS' = TRUE
        /\ pc0_a4' = pc0_a4
        /\ pc0_CS' = pc0_CS
    /\ UNCHANGED <<turn, flag0, flag1, pc0_a1, pc0_a2, pc0_a3, pc0_a5, pc1_a1, pc1_a2, pc1_a3, pc1_a5>>


\* A process exits the critical section.
cs(self) ==
    /\ IF self = 0
       THEN
        /\ pc0_CS
        /\ pc0_CS' = FALSE
        /\ pc0_a5' = TRUE
        /\ pc1_CS' = pc1_CS
        /\ pc1_a5' = pc1_a5
       ELSE
        /\ pc1_CS
        /\ pc1_CS' = FALSE
        /\ pc1_a5' = TRUE
        /\ pc0_CS' = pc0_CS
        /\ pc0_a5' = pc0_a5
    /\ UNCHANGED <<turn, flag0, flag1, pc0_a1, pc0_a2, pc0_a3, pc0_a4, pc1_a1, pc1_a2, pc1_a3, pc1_a4>>


\* A process resets its own flag to FALSE after it left the critical section.
a5(self) ==
    /\ IF self = 0
       THEN
        /\ pc0_a5
        /\ flag0' = FALSE
        /\ pc0_a5' = FALSE
        /\ pc0_a1' = TRUE
        /\ flag1' = flag1
        /\ pc1_a5' = pc1_a5
        /\ pc1_a1' = pc1_a1
       ELSE
        /\ pc1_a5
        /\ flag1' = FALSE
        /\ pc1_a5' = FALSE
        /\ pc1_a1' = TRUE
        /\ flag0' = flag0
        /\ pc0_a5' = pc0_a5
        /\ pc0_a1' = pc0_a1
    /\ UNCHANGED <<turn, pc0_a2, pc0_a3, pc0_a4, pc0_CS, pc1_a2, pc1_a3, pc1_a4, pc1_CS>>


Next == 
    \E self,other \in ProcSet : 
        \/ a1(self)
        \/ a2(self) 
        \/ a3(self, other) 
        \/ a4(self, other) 
        \/ cs(self) 
        \/ a5(self)

Spec == /\ Init /\ [][Next]_vars /\ SF_vars(Next)

Mutex == ~pc0_CS \/ ~pc1_CS

PCSoundness ==
    \* 0's
    /\ pc0_a1 => (~pc0_a2 /\ ~pc0_a3 /\ ~pc0_a4 /\ ~pc0_CS /\ ~pc0_a5)
    /\ pc0_a2 => (~pc0_a1 /\ ~pc0_a3 /\ ~pc0_a4 /\ ~pc0_CS /\ ~pc0_a5)
    /\ pc0_a3 => (~pc0_a1 /\ ~pc0_a2 /\ ~pc0_a4 /\ ~pc0_CS /\ ~pc0_a5)
    /\ pc0_a4 => (~pc0_a1 /\ ~pc0_a2 /\ ~pc0_a3 /\ ~pc0_CS /\ ~pc0_a5)
    /\ pc0_CS => (~pc0_a1 /\ ~pc0_a2 /\ ~pc0_a3 /\ ~pc0_a4 /\ ~pc0_a5)
    /\ pc0_a5 => (~pc0_a1 /\ ~pc0_a2 /\ ~pc0_a3 /\ ~pc0_a4 /\ ~pc0_CS)
    \* 1's
    /\ pc1_a1 => (~pc1_a2 /\ ~pc1_a3 /\ ~pc1_a4 /\ ~pc1_CS /\ ~pc1_a5)
    /\ pc1_a2 => (~pc1_a1 /\ ~pc1_a3 /\ ~pc1_a4 /\ ~pc1_CS /\ ~pc1_a5)
    /\ pc1_a3 => (~pc1_a1 /\ ~pc1_a2 /\ ~pc1_a4 /\ ~pc1_CS /\ ~pc1_a5)
    /\ pc1_a4 => (~pc1_a1 /\ ~pc1_a2 /\ ~pc1_a3 /\ ~pc1_CS /\ ~pc1_a5)
    /\ pc1_CS => (~pc1_a1 /\ ~pc1_a2 /\ ~pc1_a3 /\ ~pc1_a4 /\ ~pc1_a5)
    /\ pc1_a5 => (~pc1_a1 /\ ~pc1_a2 /\ ~pc1_a3 /\ ~pc1_a4 /\ ~pc1_CS)

StarvationFreedom ==
    /\ pc0_a3 ~> pc0_CS
    /\ pc1_a3 ~> pc1_CS

====
