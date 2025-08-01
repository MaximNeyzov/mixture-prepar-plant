-------------------------- MODULE MixtureFeedBuchi --------------------------

VARIABLE state

Init ==
    state = 0

iter(full, empty, reagentSpoiled, outletPump, outletPump_rise, mixtureValve) ==
    LET
        tr_0_1 == ~empty /\ full /\ mixtureValve /\ outletPump /\ ~reagentSpoiled /\ outletPump_rise
        tr_0_2 == ~empty /\ full /\ ~reagentSpoiled /\ outletPump_rise /\ (~mixtureValve \/ ~outletPump)
        tr_1_0 == empty
        tr_1_2 == ~empty /\ (~mixtureValve \/ ~outletPump)
    IN
    IF (state = 0) /\ tr_0_1 THEN state' = 1 ELSE
    IF (state = 0) /\ tr_0_2 THEN state' = 2 ELSE
    IF (state = 1) /\ tr_1_0 THEN state' = 0 ELSE
    IF (state = 1) /\ tr_1_2 THEN state' = 2 ELSE
    state' = state

=============================================================================
