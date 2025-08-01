FUNCTION_BLOCK PUBLIC Automaton
VAR
    state:    UINT := 1;
    oldState: UINT := state;
END_VAR


METHOD PUBLIC getState : UINT
BEGIN
    getState := state;
END


END_FUNCTION_BLOCK