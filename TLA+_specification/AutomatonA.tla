----------------------------- MODULE AutomatonA -----------------------------

VARIABLES
    state,
    out

Output ==
    [ preparingReagentIndicator : BOOLEAN,
      preparingMixtureIndicator : BOOLEAN,
      usingMixtureIndicator     : BOOLEAN,
      interruptIndicator        : BOOLEAN,
      prepareReagent            : BOOLEAN,
      prepareMixture            : BOOLEAN,
      stopPrepareMixture        : BOOLEAN,
      outletPump                : BOOLEAN,
      mixtureValve              : BOOLEAN,
      utilMixture               : BOOLEAN,
      initAfterDisposed         : BOOLEAN
    ]

Init ==
    /\ state = 1
    /\ out = [ preparingReagentIndicator |-> FALSE,
               preparingMixtureIndicator |-> FALSE,
               usingMixtureIndicator     |-> FALSE,
               interruptIndicator        |-> FALSE,
               prepareReagent            |-> FALSE,
               prepareMixture            |-> FALSE,
               stopPrepareMixture        |-> FALSE,
               outletPump                |-> FALSE,
               mixtureValve              |-> FALSE,
               utilMixture               |-> FALSE,
               initAfterDisposed         |-> FALSE
             ]

del(start, ready, reagentReady, mixtureReady, reagentSpoiled, empty, ackInterrupt, mixtureDisposed) ==
    LET
        tr_1_2 == start /\ ready
        tr_2_3 == reagentReady /\ ~reagentSpoiled
        tr_2_5 == reagentSpoiled
        tr_3_4 == mixtureReady
        tr_3_6 == reagentSpoiled /\ ~mixtureReady
        tr_4_1 == empty
        tr_5_1 == ackInterrupt
        tr_6_1 == mixtureDisposed /\ ackInterrupt
    IN
    IF (state = 1) /\ tr_1_2 THEN 2 ELSE
    IF (state = 2) /\ tr_2_3 THEN 3 ELSE
    IF (state = 2) /\ tr_2_5 THEN 5 ELSE
    IF (state = 3) /\ tr_3_4 THEN 4 ELSE
    IF (state = 3) /\ tr_3_6 THEN 6 ELSE
    IF (state = 4) /\ tr_4_1 THEN 1 ELSE
    IF (state = 5) /\ tr_5_1 THEN 1 ELSE
    IF (state = 6) /\ tr_6_1 THEN 1 ELSE state

lam(newState, oldState, start, ready, reagentReady, mixtureReady, reagentSpoiled, empty, ackInterrupt, mixtureDisposed) ==
    LET
        tr_1_2 == start /\ ready
        tr_2_3 == reagentReady /\ ~reagentSpoiled
        tr_3_6 == reagentSpoiled /\ ~mixtureReady
        tr_4_1 == empty
        tr_6_1 == mixtureDisposed /\ ackInterrupt
    IN
    [ preparingReagentIndicator |-> (newState = 2),
      preparingMixtureIndicator |-> (newState = 3),
      usingMixtureIndicator     |-> (newState = 4),
      interruptIndicator        |-> (newState = 5 \/ newState = 6),
      prepareReagent            |-> (oldState = 1 /\ tr_1_2),
      prepareMixture            |-> (oldState = 2 /\ tr_2_3),
      stopPrepareMixture        |-> (oldState = 3 /\ tr_3_6) \/ (oldState = 4 /\ tr_4_1),
      outletPump                |-> (newState = 4),
      mixtureValve              |-> (newState = 4),
      utilMixture               |-> (oldState = 3 /\ tr_3_6),
      initAfterDisposed         |-> (oldState = 6 /\ tr_6_1)
    ]

iter(start, ready, reagentReady, mixtureReady, reagentSpoiled, empty, ackInterrupt, mixtureDisposed) ==
    /\ state' = del(start, ready, reagentReady, mixtureReady, reagentSpoiled, empty, ackInterrupt, mixtureDisposed)
    /\ out' = lam(state', state, start, ready, reagentReady, mixtureReady, reagentSpoiled, empty, ackInterrupt, mixtureDisposed)

=============================================================================
