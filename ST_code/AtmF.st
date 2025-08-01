FUNCTION_BLOCK PUBLIC AtmF EXTENDS Automaton
VAR_INPUT
    out: OutputF;
END_VAR
VAR_OUTPUT
END_VAR
VAR
    tr_1_2: BOOL := FALSE;
    tr_2_3: BOOL := FALSE;
    tr_3_4: BOOL := FALSE;
    tr_4_1: BOOL := FALSE;
END_VAR


METHOD PRIVATE del : UINT
VAR_INPUT
    start:              BOOL := FALSE;
    init:               BOOL := FALSE;
    empty:              BOOL := FALSE;
    reagentValveClosed: BOOL := FALSE;
END_VAR
VAR
    result: UINT;
END_VAR
BEGIN
    (* update transitions *)
    tr_1_2 := start;
    tr_2_3 := empty;
    tr_3_4 := reagentValveClosed;
    tr_4_1 := init;

    result := state;

    CASE state OF
        1:  IF tr_1_2 THEN result := 2; END_IF
        2:  IF tr_2_3 THEN result := 3; END_IF
        3:  IF tr_3_4 THEN result := 4; END_IF
        4:  IF tr_4_1 THEN result := 1; END_IF
    END_CASE

    del := result;
END


METHOD PRIVATE lam : OutputF
VAR_INPUT
    state: UINT;
END_VAR
BEGIN
    lam.outletPump        := (state = 2);
    lam.reagentValveClose := (state = 3);
    lam.end               := (state = 4);
END


TYPE OutputF :
STRUCT
    outletPump:        BOOL := FALSE;
    reagentValveClose: BOOL := FALSE;
    end:               BOOL := FALSE;
END_STRUCT
END_TYPE


METHOD PUBLIC iter
VAR_INPUT
    start:              BOOL := FALSE;
    init:               BOOL := FALSE;
    empty:              BOOL := FALSE;
    reagentValveClosed: BOOL := FALSE;
END_VAR
BEGIN
    state := del(start, init, empty, reagentValveClosed);
    out := lam(state);
    oldState := state;
END


END_FUNCTION_BLOCK