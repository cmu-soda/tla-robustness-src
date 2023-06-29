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

RcvPrepare(rm) == TM!RcvPrepare(rm) /\ UNCHANGED rmVars
SndCommit(rm) == TM!SndCommit(rm) /\ UNCHANGED rmVars
SndAbort(rm) == TM!SndAbort(rm) /\ UNCHANGED rmVars

SndPrepare(rm) == UNCHANGED tmVars /\ RM!SndPrepare(rm)
RcvCommit(rm) == UNCHANGED tmVars /\ RM!RcvCommit(rm)
RcvAbort(rm) == UNCHANGED tmVars /\ RM!RcvAbort(rm)
SilentAbort(rm) == UNCHANGED tmVars /\ RM!SilentAbort(rm)

Init == TM!Init /\ RM!Init

Next ==
    \E rm \in RMs :
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ SndAbort(rm)
        \/ SndPrepare(rm)
        \/ RcvCommit(rm)
        \/ RcvAbort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK == TM!TypeOK /\ RM!TypeOK

Consistent == RM!Consistent

=============================================================================
