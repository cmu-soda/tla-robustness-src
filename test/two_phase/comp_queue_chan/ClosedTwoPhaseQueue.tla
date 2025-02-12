------------------------------- MODULE ClosedTwoPhaseQueue ----------------------------- 

VARIABLES queue, tmState, tmPrepared, rmState

vars == <<queue, rmState, tmState, tmPrepared>>
chanVars == <<queue>>
twoPhaseVars == <<rmState, tmState, tmPrepared>>

Channel == INSTANCE QueueChannel
               WITH queue <- queue

Protocol == INSTANCE TwoPhaseComp
                WITH tmState <- tmState,
                     tmPrepared <- tmPrepared,
                     rmState <- rmState

RMs == Channel!RMs \cup Protocol!RMs

Init == Channel!Init /\ Protocol!Init

RcvPrepare(rm) == Channel!RcvPrepare(rm) /\ Protocol!RcvPrepare(rm)
SndCommit(rm) == Channel!SndCommit(rm) /\ Protocol!SndCommit(rm)
SndAbort(rm) == Channel!SndAbort(rm) /\ Protocol!SndAbort(rm)

SndPrepare(rm) ==  Channel!SndPrepare(rm) /\ Protocol!SndPrepare(rm)
RcvCommit(rm) == Channel!RcvCommit(rm) /\ Protocol!RcvCommit(rm)
RcvAbort(rm) == Channel!RcvAbort(rm) /\ Protocol!RcvAbort(rm)
SilentAbort(rm) == UNCHANGED chanVars /\ Protocol!SilentAbort(rm)

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

TypeOK == Channel!TypeOK /\ Protocol!TypeOK

Consistent == Protocol!Consistent

=============================================================================
