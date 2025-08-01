FUNCTION_BLOCK PUBLIC AtmD EXTENDS Automaton
VAR_OUTPUT
    out: OutputD;
END_VAR
VAR
    tr_1_2: BOOL := FALSE;
    tr_2_3: BOOL := FALSE;
    tr_3_4: BOOL := FALSE;
    tr_4_1: BOOL := FALSE;
    tr_4_5: BOOL := FALSE;
    tr_5_1: BOOL := FALSE;
END_VAR


METHOD PRIVATE del : UINT
VAR_INPUT
    start:             BOOL := FALSE;
    materialLoaded:    BOOL := FALSE;
    concentratePoured: BOOL := FALSE;
    homogenComplete:   BOOL := FALSE;
    reagentSpoiled:    BOOL := FALSE;
END_VAR
VAR
    result: UINT;
END_VAR
BEGIN
    (* update transitions *)
    tr_1_2 := start;
    tr_2_3 := materialLoaded;
    tr_3_4 := concentratePoured;
    tr_4_1 := reagentSpoiled;
    tr_4_5 := homogenComplete AND NOT reagentSpoiled;
    tr_5_1 := TRUE;

    result := state;

    CASE state OF
        1:  IF    tr_1_2 THEN result := 2; END_IF
        2:  IF    tr_2_3 THEN result := 3; END_IF
        3:  IF    tr_3_4 THEN result := 4; END_IF
        4:  IF    tr_4_1 THEN result := 1;
            ELSIF tr_4_5 THEN result := 5; END_IF
        5:  IF    tr_5_1 THEN result := 1; END_IF
    END_CASE

    del := result;
END


METHOD PRIVATE lam : OutputD
VAR_INPUT
    state: UINT;
END_VAR
BEGIN
    lam.startReagentStabilization := (oldState = 3 AND tr_3_4);

    lam.end := (state = 5);
END


TYPE OutputD :
STRUCT
    startReagentStabilization: BOOL := FALSE;
    end:                       BOOL := FALSE;
END_STRUCT
END_TYPE


METHOD PUBLIC iter
VAR_INPUT
    start:             BOOL := FALSE;
    materialLoaded:    BOOL := FALSE;
    concentratePoured: BOOL := FALSE;
    homogenComplete:   BOOL := FALSE;
    reagentSpoiled:    BOOL := FALSE;
END_VAR
BEGIN
    state := del(start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled);
    out := lam(state);
    oldState := state;
END


METHOD PUBLIC getEndPerspective : BOOL
VAR_INPUT
    start:             BOOL := FALSE;
    materialLoaded:    BOOL := FALSE;
    concentratePoured: BOOL := FALSE;
    homogenComplete:   BOOL := FALSE;
    reagentSpoiled:    BOOL := FALSE;
END_VAR
VAR
    newState: UINT;
    newOut: OutputD;
END_VAR
BEGIN
    newState := del(start, materialLoaded, concentratePoured, homogenComplete, reagentSpoiled);
    newOut := lam(newState);
    getEndPerspective := newOut.end;
END


END_FUNCTION_BLOCK