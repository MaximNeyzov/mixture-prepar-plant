----------------------------- MODULE AutomatonD -----------------------------

VARIABLES
    state,
    out

Output ==
    [ startReagentStabilization : BOOLEAN,
      end                       : BOOLEAN
    ]

Init ==
    /\ state = 1
    /\ out = [ startReagentStabilization |-> FALSE,
               end                       |-> FALSE
             ]

del(start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled) ==
    LET
        tr_1_2 == start
        tr_2_3 == materialLoaded
        tr_3_4 == concentratePoured
        tr_4_1 == reagentSpoiled
        tr_4_5 == homogenComplete /\ ~reagentSpoiled
        tr_5_1 == TRUE
    IN
    IF (state = 1) /\ tr_1_2 THEN 2 ELSE
    IF (state = 2) /\ tr_2_3 THEN 3 ELSE
    IF (state = 3) /\ tr_3_4 THEN 4 ELSE
    IF (state = 4) /\ tr_4_1 THEN 1 ELSE
    IF (state = 4) /\ tr_4_5 THEN 5 ELSE
    IF (state = 5) /\ tr_5_1 THEN 1 ELSE state

lam(newState, oldState, start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled) ==
    LET
        tr_3_4 == concentratePoured
    IN
    [ startReagentStabilization |-> (oldState = 3) /\ tr_3_4,
      end                       |-> (newState = 5)
    ]

iter(start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled) ==
    /\ state' = del(start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled)
    /\ out' = lam(state', state, start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled)

getEndPerspective(start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled) ==
    LET
        newState == del(start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled)
        newOut == lam(newState, state, start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled)
    IN
    newOut.end

=============================================================================
