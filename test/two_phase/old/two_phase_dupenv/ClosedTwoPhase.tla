------------------------------- MODULE ClosedTwoPhase ----------------------------- 

VARIABLES tmState, tmPrepared, rmState

vars == <<rmState, tmState, tmPrepared>>
twoPhaseVars == <<rmState, tmState, tmPrepared>>

GoodRMs == INSTANCE GoodRMs

Protocol == INSTANCE TwoPhase
                WITH tmState <- tmState,
                     tmPrepared <- tmPrepared,
                     rmState <- rmState

RMs == Protocol!RMs

Init == GoodRMs!Init /\ Protocol!Init

Prepare(rm) == GoodRMs!Prepare(rm) /\ Protocol!Prepare(rm)
Commit(rm) == GoodRMs!Commit(rm) /\ Protocol!Commit(rm)
Abort(rm) == GoodRMs!Abort(rm) /\ Protocol!Abort(rm)
SilentAbort(rm) == GoodRMs!SilentAbort(rm) /\ Protocol!SilentAbort(rm)
PrepareEvil(rm) == GoodRMs!PrepareEvil(rm) /\ Protocol!PrepareEvil(rm)
CommitEvil(rm) == GoodRMs!CommitEvil(rm) /\ Protocol!CommitEvil(rm)
AbortEvil(rm) == GoodRMs!AbortEvil(rm) /\ Protocol!AbortEvil(rm)

Next ==
    \E rm \in RMs :
        \/ Prepare(rm)
        \/ Commit(rm)
        \/ Abort(rm)
        \/ SilentAbort(rm)
        \/ PrepareEvil(rm)
        \/ CommitEvil(rm)
        \/ AbortEvil(rm)

Spec == Init /\ [][Next]_vars

TypeOK == GoodRMs!TypeOK /\ Protocol!TypeOK

Consistent == Protocol!Consistent

=============================================================================
