--------------------------- MODULE B1 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES tmState, tmPrepared, queue

vars == <<queue,tmState,tmPrepared>>

RMs == {"rm1","rm2"}

msg == "msg"

theRM == "theRM"

maxLen == 5

Init ==
/\ queue = <<>>
/\ tmState = "init"
/\ tmPrepared = {}

SndPrepare(rm) ==
LET data == [msg |-> "prepare",theRM |-> rm] IN
/\ queue' = Append(queue,data)
/\ UNCHANGED <<tmState,tmPrepared>>

RcvPrepare(rm) ==
LET hd == Head(queue)
    tl == Tail(queue) IN
/\ Len(queue) > 0
/\ "prepare" = hd[msg]
/\ rm = hd[theRM]
/\ queue' = tl
/\ tmState = "init"
/\ tmPrepared' = tmPrepared \cup {rm}
/\ UNCHANGED <<tmState>>

SndCommit(rm) ==
LET data == [msg |-> "commit",theRM |-> rm] IN
/\ queue' = Append(queue,data)
/\ tmState \in {"init","commmitted"}
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>

RcvCommit(rm) ==
LET hd == Head(queue)
    tl == Tail(queue) IN
/\ Len(queue) > 0
/\ "commit" = hd[msg]
/\ rm = hd[theRM]
/\ queue' = tl
/\ UNCHANGED <<tmState,tmPrepared>>

SndAbort(rm) ==
LET data == [msg |-> "abort",theRM |-> rm] IN
/\ Len(queue) < maxLen
/\ queue' = Append(queue,data)
/\ tmState \in {"init","aborted"}
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>

RcvAbort(rm) ==
LET hd == Head(queue)
    tl == Tail(queue) IN
/\ Len(queue) > 0
/\ "abort" = hd[msg]
/\ rm = hd[theRM]
/\ queue' = tl
/\ UNCHANGED <<tmState,tmPrepared>>

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
/\ queue \in Seq([msg : {"prepare","commit","abort"},theRM : RMs])
/\ tmState \in {"init","committed","aborted"}
/\ tmPrepared \in SUBSET(RMs)
=============================================================================
