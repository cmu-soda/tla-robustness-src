------------------------------- MODULE TM ----------------------------- 

VARIABLES tmState, tmPrepared

RMs == {"rm1", "rm2"}

Init ==   
  /\ tmState = "init"
  /\ tmPrepared = {}

RcvPrepare1(rm) ==
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState>>

RcvPrepare2(rm) ==
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState>>

SndCommit1 ==
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared>>

SndCommit2 ==
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared>>

SndAbort1 ==
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared>>

SndAbort2 ==
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared>>

TypeOK ==  
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RMs

=============================================================================
