------------------------------- MODULE PerfectChannel ----------------------------- 

VARIABLES chanState

vars == <<chanState>>
RMs == {"rm1", "rm2"}

Init == chanState = "snd"

SndPrepare(rm) == 
    /\ chanState = "snd"
    /\ chanState' = "rcvPrepare"

RcvPrepare(rm) ==
    /\ chanState = "rcvPrepare"
    /\ chanState' = "snd"

SndCommit(rm) ==
    /\ chanState = "snd"
    /\ chanState' = "rcvCommit"

RcvCommit(rm) ==
    /\ chanState = "rcvCommit"
    /\ chanState' = "snd"

SndAbort(rm) ==
    /\ chanState = "snd"
    /\ chanState' = "rcvAbort"

RcvAbort(rm) ==
    /\ chanState = "rcvAbort"
    /\ chanState' = "snd"

Next ==
    \E rm \in RMs :
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ SndAbort(rm)
        \/ SndPrepare(rm)
        \/ RcvCommit(rm)
        \/ RcvAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ chanState \in {"snd","rcvPrepare","rcvCommit","rcvAbort","rcvPrepare"}

=============================================================================
