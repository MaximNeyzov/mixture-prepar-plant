FUNCTION_BLOCK PUBLIC AtmB EXTENDS Automaton
VAR_OUTPUT
    out: OutputB;
END_VAR
VAR
    tr_1_2: BOOL := FALSE;
    tr_2_3: BOOL := FALSE;
    tr_3_4: BOOL := FALSE;
	
    tr_2_1: BOOL := FALSE;
    tr_3_1: BOOL := FALSE;
    tr_4_1: BOOL := FALSE;
END_VAR


METHOD PRIVATE del : UINT
VAR_INPUT
    start:        BOOL := FALSE;
    reset:        BOOL := FALSE;
    high:         BOOL := FALSE;
    reagentAdded: BOOL := FALSE;
END_VAR
VAR
    result: UINT;
END_VAR
BEGIN
    (* update transitions *)
    tr_1_2 := start AND NOT reset;
    tr_2_3 := high AND NOT reset;
    tr_3_4 := reagentAdded AND NOT reset;
    tr_2_1 := reset;
    tr_3_1 := reset;
    tr_4_1 := reset;

    result := state;

    CASE state OF
        1:  IF    tr_1_2 THEN result := 2; END_IF
        2:  IF    tr_2_1 THEN result := 1;
            ELSIF tr_2_3 THEN result := 3; END_IF
        3:  IF    tr_3_1 THEN result := 1;
            ELSIF tr_3_4 THEN result := 4; END_IF
        4:  IF    tr_4_1 THEN result := 1; END_IF
    END_CASE

    del := result;
END


METHOD PRIVATE lam : OutputB
VAR_INPUT
    state: UINT;
    reset: BOOL;
END_VAR
BEGIN
    lam.waterValve  := (state = 2);
    lam.mixer       := (state = 3);
    lam.end         := (state = 4);
    lam.reagentFeed := (oldState = 2) AND tr_2_3;
    lam.resetSlave  := reset;
END


TYPE OutputB :
STRUCT
    waterValve:  BOOL := FALSE;
    mixer:       BOOL := FALSE;
    end:         BOOL := FALSE;
    reagentFeed: BOOL := FALSE;
    resetSlave:  BOOL := FALSE;
END_STRUCT
END_TYPE


METHOD PUBLIC iter
VAR_INPUT
    start:        BOOL := FALSE;
    reset:        BOOL := FALSE;
    high:         BOOL := FALSE;
    reagentAdded: BOOL := FALSE;
END_VAR
BEGIN
    state := del(start, reset, high, reagentAdded);
    out := lam(state, reset);
    oldState := state;
END


METHOD PUBLIC getEndPerspective : BOOL
VAR_INPUT
    start:        BOOL := FALSE;
    reset:        BOOL := FALSE;
    high:         BOOL := FALSE;
    reagentAdded: BOOL := FALSE;
END_VAR
VAR
    newState: UINT;
    newOut: OutputB;
END_VAR
BEGIN
    newState := del(start, reset, high, reagentAdded);
    newOut := lam(newState, reset);
    getEndPerspective := newOut.end;
END


END_FUNCTION_BLOCK