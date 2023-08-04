------------------------------- MODULE TwoPhaseComp ----------------------------- 

VARIABLES tmState, tmPrepared, rmState

vars == <<tmState, tmPrepared, rmState>>
tmVars == <<tmState, tmPrepared>>
rmVars == <<rmState>>

TM == INSTANCE TransactionManager
          WITH tmState <- tmState,
               tmPrepared <- tmPrepared

RM == INSTANCE ResourceManager
          WITH rmState <- rmState


RMs == TM!RMs \cup RM!RMs

Prepare(rm) == TM!Prepare(rm) /\ RM!Prepare(rm)
Commit(rm) == TM!Commit(rm) /\ RM!Commit(rm)
Abort(rm) == TM!Abort(rm) /\ RM!Abort(rm)
SilentAbort(rm) == UNCHANGED tmVars /\ RM!SilentAbort(rm)

Init == TM!Init /\ RM!Init

Next ==
    \E rm \in RMs :
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK == TM!TypeOK /\ RM!TypeOK

Consistent == RM!Consistent

=============================================================================
