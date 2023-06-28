------------------------------- MODULE QueueChannel ----------------------------- 

EXTENDS Sequences, Naturals, Integers

VARIABLES queue, chanState

vars == <<queue, chanState>>

RMs == {"rm1", "rm2"}
msg == "msg"
from == "from"


Init ==
    /\ queue = <<>>
    /\ chanState = "snd"

\* sending adds a message to the queue
\* receiving removes a message from the queue

SndPrepare(rm) == 
    LET data == [msg |-> "prepare", from |-> rm] IN
    /\ queue' = Append(queue, data)
    /\ UNCHANGED chanState

RcvPrepare(rm) ==
    LET hd == Head(queue)
        tl == Tail(queue) IN
    /\ Len(queue) > 0
    /\ "prepare" = hd[msg]
    /\ rm = hd[from]
    /\ queue' = tl
    /\ UNCHANGED chanState

SndCommit(rm) ==
    /\ chanState = "snd"
    /\ chanState' = "rcvCommit"
    /\ UNCHANGED queue

RcvCommit(rm) ==
    /\ chanState = "rcvCommit"
    /\ chanState' = "snd"
    /\ UNCHANGED queue

SndAbort(rm) ==
    /\ chanState = "snd"
    /\ chanState' = "rcvAbort"
    /\ UNCHANGED queue

RcvAbort(rm) ==
    /\ chanState = "rcvAbort"
    /\ chanState' = "snd"
    /\ UNCHANGED queue


TypeOK ==
    /\ queue \in Seq([msg : {"prepare"}, from : RMs])
    /\ chanState \in {"snd","rcvPrepare","rcvCommit","rcvAbort","rcvPrepare"}

=============================================================================
