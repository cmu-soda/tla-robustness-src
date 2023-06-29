------------------------------- MODULE QueueChannel ----------------------------- 

EXTENDS Sequences, Naturals, Integers

VARIABLES queue

vars == <<queue>>

RMs == {"rm1", "rm2"}
msg == "msg"
theRM == "theRM"
maxLen == 5


Init == queue = <<>>

\* sending adds a message to the queue
\* receiving removes a message from the queue

SndPrepare(rm) == 
    LET data == [msg |-> "prepare", theRM |-> rm] IN
    /\ queue' = Append(queue, data)

RcvPrepare(rm) ==
    LET hd == Head(queue)
        tl == Tail(queue) IN
    /\ Len(queue) > 0
    /\ "prepare" = hd[msg]
    /\ rm = hd[theRM]
    /\ queue' = tl

SndCommit(rm) ==
    LET data == [msg |-> "commit", theRM |-> rm] IN
    /\ queue' = Append(queue, data)

RcvCommit(rm) ==
    LET hd == Head(queue)
        tl == Tail(queue) IN
    /\ Len(queue) > 0
    /\ "commit" = hd[msg]
    /\ rm = hd[theRM]
    /\ queue' = tl

SndAbort(rm) ==
    LET data == [msg |-> "abort", theRM |-> rm] IN
    \* must restrict the length here since TM can abort endlessly
    /\ Len(queue) < maxLen
    /\ queue' = Append(queue, data)

RcvAbort(rm) ==
    LET hd == Head(queue)
        tl == Tail(queue) IN
    /\ Len(queue) > 0
    /\ "abort" = hd[msg]
    /\ rm = hd[theRM]
    /\ queue' = tl


TypeOK ==
    /\ queue \in Seq([msg : {"prepare","commit","abort"}, theRM : RMs])

=============================================================================
