FUNCTION_BLOCK PUBLIC AtmC EXTENDS Automaton
VAR_OUTPUT
    out: OutputC;
END_VAR
VAR
    tr_1_2:   BOOL := FALSE;
    tr_2_3:   BOOL := FALSE;
    tr_2_3_a: BOOL := FALSE;
    tr_2_3_b: BOOL := FALSE;
    tr_3_3:   BOOL := FALSE;
    tr_3_3_a: BOOL := FALSE;
    tr_3_3_b: BOOL := FALSE;
    tr_3_4:   BOOL := FALSE;
    tr_4_5:   BOOL := FALSE;
	
    tr_2_1:   BOOL := FALSE;
    tr_3_1:   BOOL := FALSE;
    tr_4_1:   BOOL := FALSE;
    tr_5_1:   BOOL := FALSE;
END_VAR


METHOD PRIVATE del : UINT
VAR_INPUT
    start:              BOOL := FALSE;
    pause:              BOOL := FALSE;
    reset:              BOOL := FALSE;
    reagentValveOpened: BOOL := FALSE;
    reagentValveClosed: BOOL := FALSE;
    full:               BOOL := FALSE;
END_VAR
VAR
    result: UINT;
END_VAR
BEGIN
    (* update transitions *)
    tr_1_2   := start AND NOT reset;
    tr_2_3_a := reagentValveOpened AND     pause AND NOT reset;
    tr_2_3_b := reagentValveOpened AND NOT pause AND NOT reset;
    tr_2_3   := tr_2_3_a OR tr_2_3_b;
    tr_3_3_a :=     pause AND NOT full AND NOT reset;
    tr_3_3_b := NOT pause AND NOT full AND NOT reset;
    tr_3_3   := tr_3_3_a OR tr_3_3_b;
    tr_3_4   := full AND NOT reset;
    tr_4_5   := reagentValveClosed AND NOT reset;

    tr_2_1 := reset;
    tr_3_1 := reset;
    tr_4_1 := reset;
    tr_5_1 := reset;

    result := state;

    CASE state OF
        1:  IF    tr_1_2 THEN result := 2; END_IF
        2:  IF    tr_2_1 THEN result := 1;
            ELSIF tr_2_3 THEN result := 3; END_IF
        3:  IF    tr_3_1 THEN result := 1;
            ELSIF tr_3_3 THEN result := 3;
            ELSIF tr_3_4 THEN result := 4; END_IF
        4:  IF    tr_4_1 THEN result := 1;
            ELSIF tr_4_5 THEN result := 5; END_IF
        5:  IF    tr_5_1 THEN result := 1; END_IF
    END_CASE

    del := result;
END


METHOD PRIVATE lam : OutputC
VAR_INPUT
    state: UINT;
END_VAR
BEGIN
    lam.reagentValveOpen  := (state = 2);
    lam.reagentValveClose := (state = 4);
    lam.end               := (state = 5);

    lam.inletPump := (oldState = 2 AND tr_2_3_b) OR
                     (oldState = 3 AND tr_3_3_b);
END


TYPE OutputC :
STRUCT
    reagentValveOpen:  BOOL := FALSE;
    reagentValveClose: BOOL := FALSE;
    inletPump:         BOOL := FALSE;
    end:               BOOL := FALSE;
END_STRUCT
END_TYPE


METHOD PUBLIC iter
VAR_INPUT
    start:              BOOL := FALSE;
    pause:              BOOL := FALSE;
    reset:              BOOL := FALSE;
    reagentValveOpened: BOOL := FALSE;
    reagentValveClosed: BOOL := FALSE;
    full:               BOOL := FALSE;
END_VAR
BEGIN
    state := del(start, pause, reset, reagentValveOpened, reagentValveClosed, full);
    out := lam(state);
    oldState := state;
END


METHOD PUBLIC getEndPerspective : BOOL
VAR_INPUT
    start:              BOOL := FALSE;
    pause:              BOOL := FALSE;
    reset:              BOOL := FALSE;
    reagentValveOpened: BOOL := FALSE;
    reagentValveClosed: BOOL := FALSE;
    full:               BOOL := FALSE;
END_VAR
VAR
    newState: UINT;
    newOut: OutputC;
END_VAR
BEGIN
    newState := del(start, pause, reset, reagentValveOpened, reagentValveClosed, full);
    newOut := lam(newState);
    getEndPerspective := newOut.end;
END


END_FUNCTION_BLOCK