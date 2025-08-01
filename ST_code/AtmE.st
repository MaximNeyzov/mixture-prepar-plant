FUNCTION_BLOCK PUBLIC AtmE EXTENDS Automaton
VAR_OUTPUT
    out: OutputE;
END_VAR
VAR
    tr_1_2:   BOOL := FALSE;
    tr_2_3:   BOOL := FALSE;
    tr_2_3_a: BOOL := FALSE;
    tr_2_3_b: BOOL := FALSE;
    tr_3_1:   BOOL := FALSE;
END_VAR


METHOD PRIVATE del : UINT
VAR_INPUT
    startStabil:     BOOL := FALSE;
    startUtil:       BOOL := FALSE;
    violated:        BOOL := FALSE;
    unstabilReagent: BOOL := FALSE;
    utilEnded:       BOOL := FALSE;
END_VAR
VAR
    result: UINT;
END_VAR
BEGIN
    (* update transitions *)
    tr_1_2   := startStabil;
    tr_2_3_a := startUtil;
    tr_2_3_b := violated AND NOT startUtil;
    tr_2_3   := tr_2_3_a OR tr_2_3_b;
    tr_3_1   := utilEnded;

    result := state;

    CASE state OF
        1:  IF tr_1_2 THEN result := 2; END_IF
        2:  IF tr_2_3 THEN result := 3; END_IF
        3:  IF tr_3_1 THEN result := 1; END_IF
    END_CASE

    del := result;
END


METHOD PRIVATE lam : OutputE
VAR_INPUT
    state: UINT;
    unstabilReagent: BOOL := FALSE;
END_VAR
BEGIN
    lam.unstabilReagent := (state = 2 AND unstabilReagent);
    lam.reagentSpoiled  := (oldState = 2 AND tr_2_3_b);
    lam.waiting         := (state = 1);
END


TYPE OutputE :
STRUCT
    unstabilReagent: BOOL := FALSE;
    reagentSpoiled:  BOOL := FALSE;
    waiting:         BOOL := TRUE;
END_STRUCT
END_TYPE


METHOD PUBLIC iter
VAR_INPUT
    startStabil:     BOOL := FALSE;
    startUtil:       BOOL := FALSE;
    violated:        BOOL := FALSE;
    unstabilReagent: BOOL := FALSE;
    utilEnded:       BOOL := FALSE;
END_VAR
BEGIN
    state := del(startStabil, startUtil, violated, unstabilReagent, utilEnded);
    out := lam(state, unstabilReagent);
    oldState := state;
END


METHOD PUBLIC getReagentSpoiledPerspective : BOOL
VAR_INPUT
    startStabil:     BOOL := FALSE;
    startUtil:       BOOL := FALSE;
    violated:        BOOL := FALSE;
    unstabilReagent: BOOL := FALSE;
    utilEnded:       BOOL := FALSE;
END_VAR
VAR
    newState: UINT;
    newOut: OutputE;
END_VAR
BEGIN
    newState := del(startStabil, startUtil, violated, unstabilReagent, utilEnded);
    newOut := lam(newState, unstabilReagent);
    getReagentSpoiledPerspective := newOut.reagentSpoiled;
END


END_FUNCTION_BLOCK