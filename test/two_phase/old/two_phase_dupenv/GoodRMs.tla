------------------------------- MODULE GoodRMs ----------------------------- 

Init == TRUE

Prepare(rm) == TRUE
Commit(rm) == TRUE
Abort(rm) == TRUE
SilentAbort(rm) == TRUE

PrepareEvil(rm) == FALSE
CommitEvil(rm) == FALSE
AbortEvil(rm) == FALSE

TypeOK == TRUE

=============================================================================
