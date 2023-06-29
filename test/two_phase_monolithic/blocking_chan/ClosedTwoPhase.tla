------------------------------- MODULE ClosedTwoPhase ----------------------------- 

VARIABLES chanState, tmState, tmPrepared, rmState

vars == <<chanState, rmState, tmState, tmPrepared>>
chanVars == <<chanState>>
twoPhaseVars == <<rmState, tmState, tmPrepared>>

Channel == INSTANCE PerfectChannel
               WITH chanState <- chanState

Protocol == INSTANCE TwoPhase
                WITH tmState <- tmState,
                     tmPrepared <- tmPrepared,
                     rmState <- rmState

RMs == Protocol!RMs

Init == Channel!Init /\ Protocol!Init

RcvPrepare(rm) == Channel!RcvPrepare(rm) /\ Protocol!RcvPrepare(rm)
SndCommit(rm) == Channel!SndCommit(rm) /\ Protocol!SndCommit(rm)
SndAbort(rm) == Channel!SndAbort(rm) /\ Protocol!SndAbort(rm)

SndPrepare(rm) ==  Channel!SndPrepare(rm) /\ Protocol!SndPrepare(rm)
SilentAbort(rm) == UNCHANGED chanVars /\ Protocol!SilentAbort(rm)
RcvCommit(rm) == Channel!RcvCommit(rm) /\ Protocol!RcvCommit(rm)
RcvAbort(rm) == Channel!RcvAbort(rm) /\ Protocol!RcvAbort(rm)

Next ==
    \E rm \in RMs :
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ SndAbort(rm)
        \/ SndPrepare(rm)
        \/ SilentAbort(rm)
        \/ RcvCommit(rm)
        \/ RcvAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK == Channel!TypeOK /\ Protocol!TypeOK

Consistent == Protocol!Consistent

=============================================================================
