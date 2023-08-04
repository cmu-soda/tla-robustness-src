---------------------------- MODULE MyTwoPhaseComp ----------------------------
VARIABLES rmState, tmState, tmPrepared

vars == <<rmState, tmState, tmPrepared>> 

RMVars == <<rmState>> 
TMVars == <<tmState, tmPrepared>> 

RM == INSTANCE ResourceManager
        WITH rmState <- rmState
TM == INSTANCE TransactionManager
        WITH tmState <- tmState,
             tmPrepared <- tmPrepared

RMs == TM!RMs \cup RM!RMs

Init == RM!Init /\ TM!Init 

Abort(rm) == RM!Abort(rm) /\ TM!Abort(rm)

Commit(rm) == RM!Commit(rm) /\ TM!Commit(rm)

Prepare(rm) == RM!Prepare(rm) /\ TM!Prepare(rm)

SilentAbort(rm) == UNCHANGED TMVars /\ RM!SilentAbort(rm)

Next == 
 \E rm \in RMs:
    \/Abort(rm) 
    \/ Commit(rm) 
    \/ Prepare(rm) 
    \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK == RM!TypeOK /\ TM!TypeOK

Consistent == RM!Consistent

=============================================================================
\* Modification History
\* Last modified Tue Jul 25 11:45:27 EDT 2023 by aprilporter
\* Created Tue Jul 11 12:01:28 EDT 2023 by aprilporter
