----------------------------- MODULE PumpBuchi -----------------------------

VARIABLE state

Init ==
    state = 0

iter(pump, full) ==
    IF (state = 0) /\ ~full /\  pump THEN state' = 1 ELSE
    IF (state = 1) /\  full          THEN state' = 0 ELSE
    IF (state = 1) /\ ~full /\ ~pump THEN state' = 2 ELSE
    state' = state

=============================================================================
