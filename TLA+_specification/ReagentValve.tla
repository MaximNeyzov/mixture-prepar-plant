---------------------------- MODULE ReagentValve ----------------------------

VARIABLES
    opened,
    closed

Init ==
    /\ opened = FALSE
    /\ closed = TRUE

iter(open, close) ==
    /\ opened' \in BOOLEAN
    /\ closed' \in BOOLEAN
    
    \* opened
    /\ (~opened /\  opened') =>  (~closed /\ ~closed' /\ open)
    /\ ( opened /\ ~opened') =>  (~closed /\ ~closed' /\ close)
    
    \* closed
    /\ (~closed /\  closed') =>  (~opened /\ ~opened' /\ close)
    /\ ( closed /\ ~closed') =>  (~opened /\ ~opened' /\ open)

(* Fairness:
    /\ []<>(open ) => []<>(~close => opened)
    /\ []<>(close) => []<>(~open  => closed)
*)

=============================================================================
