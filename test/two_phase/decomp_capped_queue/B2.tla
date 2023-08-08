--------------------------- MODULE B2 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES tmState, tmPrepared

vars == <<tmState,tmPrepared>>

RMs == {"rm1","rm2"}

msg == "msg"

theRM == "theRM"

maxLen == 5

Init ==
/\ tmState = "init"
/\ tmPrepared = {}

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = tmPrepared \cup {rm}
/\ UNCHANGED <<tmState>>

SndCommit(rm) ==
/\ tmState \in {"init","commmitted"}
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>

SndAbort(rm) ==
/\ tmState \in {"init","aborted"}
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
/\ tmState \in {"init","committed","aborted"}
/\ tmPrepared \in SUBSET(RMs)
=============================================================================
