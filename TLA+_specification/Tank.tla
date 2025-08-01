-------------------------------- MODULE Tank --------------------------------

VARIABLES
    empty,
    high,
    full

Init ==
    /\ empty = TRUE
    /\ high  = FALSE
    /\ full  = FALSE

iter(inlet, outlet) ==
    /\ empty' \in BOOLEAN
    /\ high'  \in BOOLEAN
    /\ full'  \in BOOLEAN
    
    \* empty
    /\ (~empty /\  empty') =>  (~high /\ ~high' /\ outlet)
    /\ ( empty /\ ~empty') =>  (                   inlet )
    
    \* high
    /\ (~high /\  high') =>  (~empty /\ ~empty' /\ inlet )
    /\ ( high /\ ~high') =>  (~full  /\ ~full'  /\ outlet)
    
    \* full
    /\ (~full /\  full') =>  (high /\ high' /\ inlet )
    /\ ( full /\ ~full') =>  (                 outlet)

(* Fairness:
    /\ []<>(outlet) => []<>(inlet  \/ empty)
    /\ []<>(inlet ) => []<>(outlet \/ high )
    /\ []<>(inlet ) => []<>(outlet \/ full )
*)

=============================================================================
