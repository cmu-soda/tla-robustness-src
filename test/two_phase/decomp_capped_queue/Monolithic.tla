------------------------------- MODULE Monolithic ----------------------------- 

EXTENDS Sequences, Naturals, Integers

VARIABLES queue, rmState, tmState, tmPrepared

vars == <<queue, rmState, tmState, tmPrepared>>

RMs == {"rm1", "rm2"}
msg == "msg"
theRM == "theRM"
maxLen == 5


Init ==   
  /\ queue = <<>>
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}

SndPrepare(rm) == 
  LET data == [msg |-> "prepare", theRM |-> rm] IN
  /\ Len(queue) < maxLen
  /\ queue' = Append(queue, data)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared>>

RcvPrepare(rm) ==
  LET hd == Head(queue)
      tl == Tail(queue) IN
  /\ Len(queue) > 0
  /\ "prepare" = hd[msg]
  /\ rm = hd[theRM]
  /\ queue' = tl
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState, rmState>>

SndCommit(rm) ==
  LET data == [msg |-> "commit", theRM |-> rm] IN
  /\ Len(queue) < maxLen
  /\ queue' = Append(queue, data)
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvCommit(rm) ==
  LET hd == Head(queue)
      tl == Tail(queue) IN
  /\ Len(queue) > 0
  /\ "commit" = hd[msg]
  /\ rm = hd[theRM]
  /\ queue' = tl
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared>>

SndAbort(rm) ==
  LET data == [msg |-> "abort", theRM |-> rm] IN
  \* must restrict the length here since TM can abort endlessly
  /\ Len(queue) < maxLen
  /\ queue' = Append(queue, data)
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState>>

RcvAbort(rm) ==
  LET hd == Head(queue)
      tl == Tail(queue) IN
  /\ Len(queue) > 0
  /\ "abort" = hd[msg]
  /\ rm = hd[theRM]
  /\ queue' = tl
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared>>
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, queue>>


Next ==
    \E rm \in RMs :
        \/ SndPrepare(rm)
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit(rm)
        \/ SndAbort(rm)
        \/ RcvAbort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ queue \in Seq([msg : {"prepare","commit","abort"}, theRM : RMs])
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

=============================================================================
