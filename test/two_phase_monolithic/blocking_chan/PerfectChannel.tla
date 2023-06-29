------------------------------- MODULE PerfectChannel ----------------------------- 

VARIABLES chanState

vars == <<chanState>>

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


TypeOK ==
    /\ chanState \in {"snd","rcvPrepare","rcvCommit","rcvAbort","rcvPrepare"}

=============================================================================
