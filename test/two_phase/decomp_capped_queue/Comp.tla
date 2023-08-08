--------------------------- MODULE Comp ---------------------------
VARIABLES rmState, queue

vars == <<rmState, queue>> 

A1Vars == <<rmState>> 
A2Vars == <<queue>> 

A1 == INSTANCE A1
		WITH rmState <- rmState
A2 == INSTANCE A2
		WITH queue <- queue

RMs == A1!RMs

Init == A1!Init /\ A2!Init 

SndPrepare(rm) == A1!SndPrepare(rm) /\ A2!SndPrepare(rm)

RcvAbort(rm) == A1!RcvAbort(rm) /\ A2!RcvAbort(rm)

RcvCommit(rm) == A1!RcvCommit(rm) /\ A2!RcvCommit(rm)

SilentAbort(rm) == UNCHANGED A2Vars /\ A1!SilentAbort(rm)

SndAbort(rm) == UNCHANGED A1Vars /\ A2!SndAbort(rm)

RcvPrepare(rm) == UNCHANGED A1Vars /\ A2!RcvPrepare(rm)

SndCommit(rm) == UNCHANGED A1Vars /\ A2!SndCommit(rm)

Next == 
 \E rm \in RMs:
    \/SndPrepare(rm) 
    \/ RcvAbort(rm) 
    \/ RcvCommit(rm) 
    \/ SilentAbort(rm) 
    \/ SndAbort(rm) 
    \/ RcvPrepare(rm) 
    \/ SndCommit(rm)

Spec == Init /\ [][Next]_vars

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")
=============================================================================
