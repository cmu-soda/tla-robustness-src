------------------------------- MODULE ClosedTwoPhase ----------------------------- 

VARIABLES chanState, tmState, tmPrepared, rmState1, rmState2

vars == <<chanState, rmState1, tmState, tmPrepared>>
chanVars == <<chanState>>
twoPhaseVars == <<rmState1, tmState, tmPrepared>>

Channel == INSTANCE PerfectChannel
             WITH chanState <- chanState

Protocol == INSTANCE TwoPhase
                WITH tmState <- tmState,
                     tmPrepared <- tmPrepared,
                     rmState1 <- rmState1,
                     rmState2 <- rmState2

RMs == Protocol!RMs

Init == Channel!Init /\ Protocol!Init

RcvPrepare1(rm) == Channel!RcvPrepare1(rm) /\ Protocol!RcvPrepare1(rm)
RcvPrepare2(rm) == Channel!RcvPrepare2(rm) /\ Protocol!RcvPrepare2(rm)
SndCommit1 == Channel!SndCommit1 /\ Protocol!SndCommit1
SndCommit2 == Channel!SndCommit2 /\ Protocol!SndCommit2
SndAbort1 == Channel!SndAbort1 /\ Protocol!SndAbort1
SndAbort2 == Channel!SndAbort2 /\ Protocol!SndAbort2

SndPrepare1(rm) == Channel!SndPrepare1(rm) /\ Protocol!SndPrepare1(rm)
SilentAbort1(rm) == UNCHANGED chanVars /\ Protocol!SilentAbort1(rm)
RcvCommit1(rm) == Channel!RcvCommit1(rm) /\ Protocol!RcvCommit1(rm)
RcvAbort1(rm) == Channel!RcvAbort1(rm) /\ Protocol!RcvAbort1(rm)

SndPrepare2(rm) == Channel!SndPrepare2(rm) /\ Protocol!SndPrepare2(rm)
SilentAbort2(rm) == UNCHANGED chanVars /\ Protocol!SilentAbort2(rm)
RcvCommit2(rm) == Channel!RcvCommit2(rm) /\ Protocol!RcvCommit2(rm)
RcvAbort2(rm) == Channel!RcvAbort2(rm) /\ Protocol!RcvAbort2(rm)

Next ==
    \E rm \in RMs :
        \/ RcvPrepare1(rm)
        \/ RcvPrepare2(rm)
        \/ SndCommit1
        \/ SndCommit2
        \/ SndAbort1
        \/ SndAbort2
        \/ SndPrepare1(rm)
        \/ SilentAbort1(rm)
        \/ RcvCommit1(rm)
        \/ RcvAbort1(rm)
        \/ SndPrepare2(rm)
        \/ SilentAbort2(rm)
        \/ RcvCommit2(rm)
        \/ RcvAbort2(rm)

Spec == Init /\ [][Next]_vars

TypeOK == Channel!TypeOK /\ Protocol!TypeOK

Consistent == Protocol!Consistent

=============================================================================
