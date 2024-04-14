------------------------------ MODULE Simple ------------------------------
\* benchmark: tla-simple

(***************************************************************************)
(* This is a trivial example from the document "Teaching Conccurrency"     *)
(* that appeared in                                                        *)
(*                                                                         *)
(*     ACM SIGACT News Volume 40, Issue 1 (March 2009), 58-62              *)
(*                                                                         *)
(* A copy of that article is at                                            *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/pubs/teaching-concurrency.pdf       *)
(*                                                                         *)
(* It is also the example in Section 7.2 of "Proving Safety Properties",   *)
(* which is at                                                             *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers\*, TLAPS

N == 5
ASSUME NAssump ==  (N \in Nat) /\ (N > 0)

(****************************************************************************
Here is the algorithm in PlusCal.  It's easy to understand if you think
of the N processes, numbered from 0 through N-1, as arranged in a
circle, with processes (i-1) % N and (i+1) % N being the processes on
either side of process i.

algorithm Simple {
    variables x = [i \in 0..(N-1) |-> 0], y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..N-1) {
      a: x[self] := 1 ;
      b: y[self] := x[(self-1) % N]
    }
}
****************************************************************************)
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ x = [i \in 0..(N-1) |-> 0]
        /\ y = [i \in 0..(N-1) |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ x' = [x EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ y' = [y EXCEPT ![self] = x[(self-1) % N]]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a(self) \/ b(self)

Next == \E self \in 0..N-1: proc(self)

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(***************************************************************************)
(* The property of this algorithm we want to prove is that, when all the   *)
(* processses have terminated, y[i] equals 1 for at least one process i.   *)
(* This property is express by the invariance of the following formula     *)
(* PCorrect.  In other words, we have to prove the theorem                 *)
(*                                                                         *)
(*    Spec => []PCorrect                                                   *)
(***************************************************************************)
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") => 
                (\E i \in 0..(N-1) : y[i] = 1)

(***************************************************************************)
(* Proving the invariance of PCorrect requires finding an inductive        *)
(* invariant Inv that implies it.  As usual, the inductive invariant       *)
(* includes a type-correctness invariant, which is the following formula   *)
(* TypeOK.                                                                 *)
(***************************************************************************)
TypeOK == /\ x \in [0..(N-1) -> {0,1}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"a", "b", "Done"}]
 
=============================================================================
