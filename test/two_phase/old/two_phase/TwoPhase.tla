------------------------------- MODULE TwoPhase ----------------------------- 

VARIABLES tmState, tmPrepared, rmState1, rmState2

vars == <<rmState1, tmState, tmPrepared>>
tmVars == <<tmState, tmPrepared>>
rm1Vars == <<rmState1>>
rm2Vars == <<rmState2>>

TM == INSTANCE TM
          WITH tmState <- tmState,
               tmPrepared <- tmPrepared

RM1 == INSTANCE RM1
          WITH rmState <- rmState1

RM2 == INSTANCE RM2
          WITH rmState <- rmState2

RMs == TM!RMs

Init == TM!Init /\ RM1!Init /\ RM2!Init

RcvPrepare1(rm) == TM!RcvPrepare1(rm) /\ UNCHANGED rm1Vars /\ UNCHANGED rm2Vars
RcvPrepare2(rm) == TM!RcvPrepare2(rm) /\ UNCHANGED rm1Vars /\ UNCHANGED rm2Vars
SndCommit1 == TM!SndCommit1 /\ UNCHANGED rm1Vars /\ UNCHANGED rm2Vars
SndCommit2 == TM!SndCommit2 /\ UNCHANGED rm1Vars /\ UNCHANGED rm2Vars
SndAbort1 == TM!SndAbort1 /\ UNCHANGED rm1Vars /\ UNCHANGED rm2Vars
SndAbort2 == TM!SndAbort2 /\ UNCHANGED rm1Vars /\ UNCHANGED rm2Vars

SndPrepare1(rm) == UNCHANGED tmVars /\ RM1!SndPrepare1(rm) /\ UNCHANGED rm2Vars
SilentAbort1(rm) == UNCHANGED tmVars /\ RM1!SilentAbort1(rm) /\ UNCHANGED rm2Vars
RcvCommit1(rm) == UNCHANGED tmVars /\ RM1!RcvCommit1(rm) /\ UNCHANGED rm2Vars
RcvAbort1(rm) == UNCHANGED tmVars /\ RM1!RcvAbort1(rm) /\ UNCHANGED rm2Vars

SndPrepare2(rm) == UNCHANGED tmVars /\ UNCHANGED rm1Vars /\ RM2!SndPrepare2(rm)
SilentAbort2(rm) == UNCHANGED tmVars /\ UNCHANGED rm1Vars /\ RM2!SilentAbort2(rm)
RcvCommit2(rm) == UNCHANGED tmVars /\ UNCHANGED rm1Vars /\ RM2!RcvCommit2(rm)
RcvAbort2(rm) == UNCHANGED tmVars /\ UNCHANGED rm1Vars /\ RM2!RcvAbort2(rm)

Next ==
    \E rm \in RMs :
        \/ RcvPrepare1(rm)
        \/ RcvPrepare2(rm)
        \/ SndCommit1
        \/ SndCommit2
        \/ SndAbort1
        \/ SndAbort2
        \/ SndPrepare1(rm)
        \/ SilentAbort1(rm)
        \/ RcvCommit1(rm)
        \/ RcvAbort1(rm)
        \/ SndPrepare2(rm)
        \/ SilentAbort2(rm)
        \/ RcvCommit2(rm)
        \/ RcvAbort2(rm)

Spec == Init /\ [][Next]_vars

TypeOK == TM!TypeOK /\ RM1!TypeOK /\ RM2!TypeOK

Consistent ==
    /\ ~(rmState1 = "aborted" /\ rmState2 = "committed")
    /\ ~(rmState2 = "aborted" /\ rmState1 = "committed")

=============================================================================
