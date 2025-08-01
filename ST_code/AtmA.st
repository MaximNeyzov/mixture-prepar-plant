FUNCTION_BLOCK PUBLIC AtmA EXTENDS Automaton
VAR_OUTPUT
    out: OutputA;
END_VAR
VAR
    tr_1_2: BOOL := FALSE;
    tr_2_3: BOOL := FALSE;
    tr_2_5: BOOL := FALSE;
    tr_3_4: BOOL := FALSE;
    tr_3_6: BOOL := FALSE;
    tr_4_1: BOOL := FALSE;
    tr_5_1: BOOL := FALSE;
    tr_6_1: BOOL := FALSE;
END_VAR


METHOD PRIVATE del : UINT
VAR_INPUT
    start:           BOOL := FALSE;
    ready:           BOOL := FALSE;
    reagentReady:    BOOL := FALSE;
    mixtureReady:    BOOL := FALSE;
    reagentSpoiled:  BOOL := FALSE;
    empty:           BOOL := FALSE;
    ackInterrupt:    BOOL := FALSE;
    mixtureDisposed: BOOL := FALSE;
END_VAR
VAR
    result: UINT;
END_VAR
BEGIN
    (* update transitions *)
    tr_1_2 := start AND ready;
    tr_2_3 := reagentReady AND NOT reagentSpoiled;
    tr_2_5 := reagentSpoiled;
    tr_3_4 := mixtureReady;
    tr_3_6 := reagentSpoiled AND NOT mixtureReady;
    tr_4_1 := empty;
    tr_5_1 := ackInterrupt;
    tr_6_1 := mixtureDisposed AND ackInterrupt;

    result := state;

    CASE state OF
        1:  IF    tr_1_2 THEN result := 2; END_IF
        2:  IF    tr_2_3 THEN result := 3;
            ELSIF tr_2_5 THEN result := 5; END_IF
        3:  IF    tr_3_4 THEN result := 4;
            ELSIF tr_3_6 THEN result := 6; END_IF
        4:  IF    tr_4_1 THEN result := 1; END_IF
        5:  IF    tr_5_1 THEN result := 1; END_IF
        6:  IF    tr_6_1 THEN result := 1; END_IF
    END_CASE

    del := result;
END


METHOD PRIVATE lam : OutputA
VAR_INPUT
    state: UINT;
END_VAR
BEGIN
    lam.preparingReagentIndicator := (state = 2);
    lam.preparingMixtureIndicator := (state = 3);
    lam.usingMixtureIndicator     := (state = 4);
    lam.interruptIndicator        := (state = 5) OR (state = 6);

    lam.prepareReagent     := (oldState = 1 AND tr_1_2);
    lam.prepareMixture     := (oldState = 2 AND tr_2_3);
    lam.stopPrepareMixture := (oldState = 3 AND tr_3_6) OR (oldState = 4 AND tr_4_1);

    lam.outletPump        := (state = 4);
    lam.mixtureValve      := (state = 4);
    lam.utilMixture       := (oldState = 3 AND tr_3_6);
    lam.initAfterDisposed := (oldState = 6 AND tr_6_1);
END


TYPE OutputA :
STRUCT
    preparingReagentIndicator: BOOL := FALSE;
    preparingMixtureIndicator: BOOL := FALSE;
    usingMixtureIndicator:     BOOL := FALSE;
    interruptIndicator:        BOOL := FALSE;
    prepareReagent:            BOOL := FALSE;
    prepareMixture:            BOOL := FALSE;
    stopPrepareMixture:        BOOL := FALSE;
    outletPump:                BOOL := FALSE;
    mixtureValve:              BOOL := FALSE;
    utilMixture:               BOOL := FALSE;
    initAfterDisposed:         BOOL := FALSE;
END_STRUCT
END_TYPE


METHOD PUBLIC iter
VAR_INPUT
    start:           BOOL := FALSE;
    ready:           BOOL := FALSE;
    reagentReady:    BOOL := FALSE;
    mixtureReady:    BOOL := FALSE;
    reagentSpoiled:  BOOL := FALSE;
    empty:           BOOL := FALSE;
    ackInterrupt:    BOOL := FALSE;
    mixtureDisposed: BOOL := FALSE;
END_VAR
BEGIN
    state := del(start, ready, reagentReady, mixtureReady, reagentSpoiled, empty, ackInterrupt, mixtureDisposed);
    out := lam(state);
    oldState := state;
END


END_FUNCTION_BLOCK