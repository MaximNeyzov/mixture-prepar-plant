----------------------------- MODULE AutomatonB -----------------------------

VARIABLES
    state,
    out

Output ==
    [ waterValve  : BOOLEAN,
      mixer       : BOOLEAN,
      end         : BOOLEAN,
      reagentFeed : BOOLEAN,
      resetSlave  : BOOLEAN
    ]

Init ==
    /\ state = 1
    /\ out = [ waterValve  |-> FALSE,
               mixer       |-> FALSE,
               end         |-> FALSE,
               reagentFeed |-> FALSE,
               resetSlave  |-> FALSE
             ]

del(start, reset, high, reagentAdded) ==
    LET
        tr_1_2 == start /\ ~reset
        tr_2_3 == high /\ ~reset
        tr_3_4 == reagentAdded /\ ~reset
        tr_2_1 == reset
        tr_3_1 == reset
        tr_4_1 == reset
    IN
    IF (state = 1) /\ tr_1_2 THEN 2 ELSE
    IF (state = 2) /\ tr_2_1 THEN 1 ELSE
    IF (state = 2) /\ tr_2_3 THEN 3 ELSE
    IF (state = 3) /\ tr_3_1 THEN 1 ELSE
    IF (state = 3) /\ tr_3_4 THEN 4 ELSE
    IF (state = 4) /\ tr_4_1 THEN 1 ELSE state

lam(newState, oldState, start, reset, high, reagentAdded) ==
    LET
        tr_2_3 == high /\ ~reset
    IN
    [ waterValve  |-> (newState = 2),
      mixer       |-> (newState = 3),
      end         |-> (newState = 4),
      reagentFeed |-> (oldState = 2) /\ tr_2_3,
      resetSlave  |-> reset
    ]

iter(start, reset, high, reagentAdded) ==
    /\ state' = del(start, reset, high, reagentAdded)
    /\ out' = lam(state', state, start, reset, high, reagentAdded)

getEndPerspective(start, reset, high, reagentAdded) ==
    LET
        newState == del(start, reset, high, reagentAdded)
        newOut == lam(newState, state, start, reset, high, reagentAdded)
    IN
    newOut.end

=============================================================================
