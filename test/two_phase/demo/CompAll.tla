------------------------------- MODULE CompAll ----------------------------- 

VARIABLES queue, tmState, tmPrepared, rmState

vars == <<queue, rmState, tmState, tmPrepared>>
varsA1 == <<rmState>>
varsA2 == <<queue>>
varsB2 == <<tmState, tmPrepared>>

A1 == INSTANCE A1
              WITH rmState <- rmState

A2 == INSTANCE A2
              WITH queue <- queue

B2 == INSTANCE B2
              WITH tmState <- tmState,
                   tmPrepared <- tmPrepared

RMs == {"rm1", "rm2"}
msg == "msg"
theRM == "theRM"
maxLen == 5

Init == A1!Init /\ A2!Init /\ B2!Init

RcvPrepare(rm) == UNCHANGED varsA1 /\ A2!RcvPrepare(rm) /\ B2!RcvPrepare(rm)
SndCommit(rm) == UNCHANGED varsA1 /\ A2!SndCommit(rm) /\ B2!SndCommit(rm)
SndAbort(rm) == UNCHANGED varsA1 /\ A2!SndAbort(rm) /\ B2!SndAbort(rm)

SndPrepare(rm) ==  A1!SndPrepare(rm) /\ A2!SndPrepare(rm) /\ UNCHANGED varsB2
RcvCommit(rm) == A1!RcvCommit(rm) /\ A2!RcvCommit(rm) /\ UNCHANGED varsB2
RcvAbort(rm) == A1!RcvAbort(rm) /\ A2!RcvAbort(rm) /\ UNCHANGED varsB2
SilentAbort(rm) == A1!SilentAbort(rm) /\ UNCHANGED varsA2 /\ UNCHANGED varsB2

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

TypeOK == A1!TypeOK /\ A2!TypeOK /\ B2!TypeOK

Consistent == A1!Consistent

=============================================================================
