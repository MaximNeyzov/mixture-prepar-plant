----------------------------- MODULE AutomatonE -----------------------------

VARIABLES
    state,
    out

Output ==
    [ unstabilReagent : BOOLEAN,
      reagentSpoiled  : BOOLEAN,
      waiting         : BOOLEAN
    ]

Init ==
    /\ state = 1
    /\ out = [ unstabilReagent |-> FALSE,
               reagentSpoiled  |-> FALSE,
               waiting         |-> TRUE
             ]

del(startStabil, startUtil, violated, unstabilReagent, utilEnded) ==
    LET
        tr_1_2   == startStabil
        tr_2_3_a == startUtil
        tr_2_3_b == violated /\ ~startUtil
        tr_2_3   == tr_2_3_a \/ tr_2_3_b
        tr_3_1   == utilEnded
    IN
    IF (state = 1) /\ tr_1_2 THEN 2 ELSE
    IF (state = 2) /\ tr_2_3 THEN 3 ELSE
    IF (state = 3) /\ tr_3_1 THEN 1 ELSE state

lam(newState, oldState, startStabil, startUtil, violated, unstabilReagent, utilEnded) ==
    LET
        tr_2_3_b == violated /\ ~startUtil
    IN
    [ unstabilReagent |-> (newState = 2 /\ unstabilReagent),
      reagentSpoiled  |-> (oldState = 2 /\ tr_2_3_b),
      waiting         |-> (newState = 1)
    ]

iter(startStabil, startUtil, violated, unstabilReagent, utilEnded) ==
    /\ state' = del(startStabil, startUtil, violated, unstabilReagent, utilEnded)
    /\ out' = lam(state', state, startStabil, startUtil, violated, unstabilReagent, utilEnded)

getReagentSpoiledPerspective(startStabil, startUtil, violated, unstabilReagent, utilEnded) ==
    LET
        newState == del(startStabil, startUtil, violated, unstabilReagent, utilEnded)
        newOut == lam(newState, state, startStabil, startUtil, violated, unstabilReagent, utilEnded)
    IN
    newOut.reagentSpoiled

=============================================================================
