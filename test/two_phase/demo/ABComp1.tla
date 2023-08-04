------------------------------- MODULE ABComp1 ----------------------------- 

VARIABLES queue, tmState, tmPrepared, rmState

vars == <<queue, rmState, tmState, tmPrepared>>
varsA == <<rmState>>
varsB == <<queue, tmState, tmPrepared>>

A == INSTANCE A1
              WITH rmState <- rmState

B == INSTANCE B1
              WITH tmState <- tmState,
                   tmPrepared <- tmPrepared,
                   queue <- queue

RMs == {"rm1", "rm2"}
msg == "msg"
theRM == "theRM"
maxLen == 5

Init == A!Init /\ B!Init

RcvPrepare(rm) == UNCHANGED varsA /\ B!RcvPrepare(rm)
SndCommit(rm) == UNCHANGED varsA /\ B!SndCommit(rm)
SndAbort(rm) == UNCHANGED varsA /\ B!SndAbort(rm)

SndPrepare(rm) ==  A!SndPrepare(rm) /\ B!SndPrepare(rm)
RcvCommit(rm) == A!RcvCommit(rm) /\ B!RcvCommit(rm)
RcvAbort(rm) == A!RcvAbort(rm) /\ B!RcvAbort(rm)
SilentAbort(rm) == A!SilentAbort(rm) /\ UNCHANGED varsB

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

TypeOK == A!TypeOK /\ B!TypeOK

Consistent == A!Consistent

=============================================================================
