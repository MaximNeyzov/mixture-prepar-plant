PROGRAM PLC_PRG
VAR
    model: ControlModel;
    state: ModelState;

    (* Inputs *)
    start:              BOOL := FALSE;
    ackInterrupt:       BOOL := FALSE;
    full:               BOOL := FALSE;
    high:               BOOL := FALSE;
    empty:              BOOL := TRUE;
    reagentValveOpened: BOOL := FALSE;
    reagentValveClosed: BOOL := TRUE;
    materialLoaded:     BOOL := FALSE;
    concentratePoured:  BOOL := FALSE;
    homogenComplete:    BOOL := FALSE;
    violated:           BOOL := FALSE;
    unstabilReagent:    BOOL := FALSE;
    utilEnded:          BOOL := FALSE;
END_VAR
BEGIN
    model.iter( start,
                ackInterrupt,
                full,
                high,
                empty,
                reagentValveOpened,
                reagentValveClosed,
                materialLoaded,
                concentratePoured,
                homogenComplete,
                violated,
                unstabilReagent,
                utilEnded );
    state := model.getState();
END_PROGRAM