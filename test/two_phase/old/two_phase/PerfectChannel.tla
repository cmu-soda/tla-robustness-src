------------------------------- MODULE PerfectChannel ----------------------------- 

VARIABLES chanState

vars == <<chanState>>

Init == chanState = "snd"

RcvPrepare1(rm) == 
    /\ chanState = "rcvPrepare1"
    /\ chanState' = "snd"

RcvPrepare2(rm) == 
    /\ chanState = "rcvPrepare2"
    /\ chanState' = "snd"

SndCommit1 ==
    /\ chanState = "snd"
    /\ chanState' = "rcvCommit1"

SndCommit2 ==
    /\ chanState = "snd"
    /\ chanState' = "rcvCommit2"

SndAbort1 ==
    /\ chanState = "snd"
    /\ chanState' = "rcvAbort1"

SndAbort2 ==
    /\ chanState = "snd"
    /\ chanState' = "rcvAbort2"
  

SndPrepare1(rm) == 
    /\ chanState = "snd"
    /\ chanState' = "rcvPrepare1"
  
RcvCommit1(rm) ==
    /\ chanState = "rcvCommit1"
    /\ chanState' = "snd"

RcvAbort1(rm) ==
    /\ chanState = "rcvAbort1"
    /\ chanState' = "snd"


SndPrepare2(rm) == 
    /\ chanState = "snd"
    /\ chanState' = "rcvPrepare2"
  
RcvCommit2(rm) ==
    /\ chanState = "rcvCommit2"
    /\ chanState' = "snd"

RcvAbort2(rm) ==
    /\ chanState = "rcvAbort2"
    /\ chanState' = "snd"

TypeOK ==
    /\ chanState \in {"snd", "rcvPrepare1", "rcvPrepare1",
            "rcvCommit1", "rcvCommit2", "rcvAbort1", "rcvAbort2",
            "rcvPrepare1", "rcvPrepare2"}

=============================================================================
