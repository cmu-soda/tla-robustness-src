------------------------------- MODULE MultiChannel ----------------------------- 

VARIABLES chans

numChans == 2

vars == <<chans>>

Init == chans = [i \in 1..numChans |-> "ready"]


=============================================================================
