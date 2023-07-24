------------------------------- MODULE A2 ----------------------------- 

EXTENDS Sequences, Naturals, Integers

VARIABLES queue

vars == <<queue>>

RMs == {"rm1", "rm2"}
msg == "msg"
theRM == "theRM"
maxLen == 5

Init ==   
  /\ queue = <<>>

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
  /\ queue \in Seq([msg : {"prepare","commit","abort"}, theRM : RMs])

=============================================================================
