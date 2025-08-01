----------------------------- MODULE AutomatonF -----------------------------

VARIABLES
    state,
    out

Output ==
    [ outletPump        : BOOLEAN,
      reagentValveClose : BOOLEAN,
      end               : BOOLEAN
    ]

Init ==
    /\ state = 1
    /\ out = [ outletPump        |-> FALSE,
               reagentValveClose |-> FALSE,
               end               |-> FALSE
             ]

del(start, init, empty, reagentValveClosed) ==
    LET
        tr_1_2 == start
        tr_2_3 == empty
        tr_3_4 == reagentValveClosed
        tr_4_1 == init
    IN
    IF (state = 1) /\ tr_1_2 THEN 2 ELSE
    IF (state = 2) /\ tr_2_3 THEN 3 ELSE
    IF (state = 3) /\ tr_3_4 THEN 4 ELSE
    IF (state = 4) /\ tr_4_1 THEN 1 ELSE state

lam(newState) ==
    [ outletPump        |-> (newState = 2),
      reagentValveClose |-> (newState = 3),
      end               |-> (newState = 4)
    ]

iter(start, init, empty, reagentValveClosed) ==
    /\ state' = del(start, init, empty, reagentValveClosed)
    /\ out' = lam(state')

=============================================================================
