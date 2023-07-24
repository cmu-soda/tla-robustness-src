--------------------------- MODULE CoffeeMachine ---------------------------
EXTENDS Naturals
VARIABLES t

SelectCoffee == (t = 0 /\ t' = 212) \/ (t = 1 /\ t' = 213)

SelectTea == (t = 213 /\ t' = 215)

SelectHotChocolate == t' = 212

Init == t \in {0, 1}

Next == \/ SelectCoffee
        \/ SelectTea
        \/ SelectHotChocolate
 
Spec == Init /\ [][Next]_t

Safety == t < 220

=============================================================================
\* Modification History
\* Last modified Wed Jul 12 09:26:43 EDT 2023 by aprilporter
\* Created Tue Jun 06 15:41:20 EDT 2023 by aprilporter
