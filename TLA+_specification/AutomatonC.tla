----------------------------- MODULE AutomatonC -----------------------------

VARIABLES
    state,
    out

Output ==
    [ reagentValveOpen  : BOOLEAN,
      reagentValveClose : BOOLEAN,
      inletPump         : BOOLEAN,
      end               : BOOLEAN
    ]

Init ==
    /\ state = 1
    /\ out = [ reagentValveOpen  |-> FALSE,
               reagentValveClose |-> FALSE,
               inletPump         |-> FALSE,
               end               |-> FALSE
             ]

del(start, pause, reset, reagentValveOpened, reagentValveClosed, full) ==
    LET
        tr_1_2   == start /\ ~reset
        tr_2_3_a == reagentValveOpened /\  pause /\ ~reset
        tr_2_3_b == reagentValveOpened /\ ~pause /\ ~reset
        tr_2_3   == tr_2_3_a \/ tr_2_3_b
        tr_3_3_a ==  pause /\ ~full /\ ~reset
        tr_3_3_b == ~pause /\ ~full /\ ~reset
        tr_3_3   == tr_3_3_a \/ tr_3_3_b
        tr_3_4   == full /\ ~reset
        tr_4_5   == reagentValveClosed /\ ~reset
        tr_2_1   == reset
        tr_3_1   == reset
        tr_4_1   == reset
        tr_5_1   == reset
    IN
    IF (state = 1) /\ tr_1_2 THEN 2 ELSE
    IF (state = 2) /\ tr_2_1 THEN 1 ELSE
    IF (state = 2) /\ tr_2_3 THEN 3 ELSE
    IF (state = 3) /\ tr_3_1 THEN 1 ELSE
    IF (state = 3) /\ tr_3_3 THEN 3 ELSE
    IF (state = 3) /\ tr_3_4 THEN 4 ELSE
    IF (state = 4) /\ tr_4_1 THEN 1 ELSE
    IF (state = 4) /\ tr_4_5 THEN 5 ELSE
    IF (state = 5) /\ tr_5_1 THEN 1 ELSE state

lam(newState, oldState, start, pause, reset, reagentValveOpened, reagentValveClosed, full) ==
    LET
        tr_2_3_b == reagentValveOpened /\ ~pause /\ ~reset
        tr_3_3_b == ~pause /\ ~full /\ ~reset
    IN
    [ reagentValveOpen  |-> (newState = 2),
      reagentValveClose |-> (newState = 4),
      end               |-> (newState = 5),
      inletPump         |-> \/ (oldState = 2 /\ tr_2_3_b)
                            \/ (oldState = 3 /\ tr_3_3_b)
    ]

iter(start, pause, reset, reagentValveOpened, reagentValveClosed, full) ==
    /\ state' = del(start, pause, reset, reagentValveOpened, reagentValveClosed, full)
    /\ out' = lam(state', state, start, pause, reset, reagentValveOpened, reagentValveClosed, full)

getEndPerspective(start, pause, reset, reagentValveOpened, reagentValveClosed, full) ==
    LET
        newState == del(start, pause, reset, reagentValveOpened, reagentValveClosed, full)
        newOut == lam(newState, state, start, pause, reset, reagentValveOpened, reagentValveClosed, full)
    IN
    newOut.end

=============================================================================
