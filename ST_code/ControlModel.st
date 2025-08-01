FUNCTION_BLOCK PUBLIC ControlModel
VAR_OUTPUT
    out: OutputModel;
END_VAR
VAR
    atmA: AtmA;
    atmB: AtmB;
    atmC: AtmC;
    atmD: AtmD;
    atmE: AtmE;
    atmF: AtmF;
	
    atmE_waitingRetro: BOOL := FALSE;
    atmF_endRetro:     BOOL := FALSE;
	
    atmB_endPersp: BOOL := FALSE;
    atmC_endPersp: BOOL := FALSE;
    atmD_endPersp: BOOL := FALSE;
    atmE_reagentSpoiledPersp: BOOL := FALSE;
END_VAR


METHOD PUBLIC iter
VAR_INPUT
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
    (* Retrospectives *)
    atmE_waitingRetro := atmE.out.waiting;
    atmF_endRetro     := atmF.out.end;

    (* Perspectives *)
    atmC_endPersp := atmC.getEndPerspective( start := FALSE,
                                             pause := FALSE,
                                             reset := FALSE,
                                             reagentValveOpened := reagentValveOpened,
                                             reagentValveClosed := reagentValveClosed,
                                             full := full );
    atmB_endPersp := atmB.getEndPerspective( start := FALSE,
                                             reset := FALSE,
                                             high := high,
                                             reagentAdded := atmC_endPersp );
    atmE_reagentSpoiledPersp := atmE.getReagentSpoiledPerspective( startStabil := FALSE,
                                                                   startUtil := atmB_endPersp,
                                                                   violated := violated,
                                                                   unstabilReagent := unstabilReagent,
                                                                   utilEnded := utilEnded );
    atmD_endPersp := atmD.getEndPerspective( start := FALSE,
                                             materialLoaded := materialLoaded,
                                             concentratePoured := concentratePoured,
                                             homogenComplete := homogenComplete,
                                             reagentSpoiled := atmE_reagentSpoiledPersp );

    (* Automaton A *)
    atmA.iter( start := start,
               ready := atmE_waitingRetro,
               reagentReady := atmD_endPersp,
               mixtureReady := atmB_endPersp,
               reagentSpoiled := atmE_reagentSpoiledPersp,
               empty := empty,
               ackInterrupt := ackInterrupt,
               mixtureDisposed := atmF_endRetro );

    (* Automaton D *)
    atmD.iter( start := atmA.out.prepareReagent,
               materialLoaded := materialLoaded,
               concentratePoured := concentratePoured,
               homogenComplete := homogenComplete,
               reagentSpoiled := atmE_reagentSpoiledPersp );

    (* Automaton E *)
    atmE.iter( startStabil := atmD.out.startReagentStabilization,
               startUtil := atmB_endPersp,
               violated := violated,
               unstabilReagent := unstabilReagent,
               utilEnded := utilEnded );

    (* Automaton B *)
    atmB.iter( start := atmA.out.prepareMixture,
               reset := atmA.out.stopPrepareMixture,
               high := high,
               reagentAdded := atmC_endPersp );

    (* Automaton C *)
    atmC.iter( start := atmB.out.reagentFeed,
               pause := atmE.out.unstabilReagent,
               reset := atmB.out.resetSlave,
               reagentValveOpened := reagentValveOpened,
               reagentValveClosed := reagentValveClosed,
               full := full );

    (* Automaton F *)
    atmF.iter( start := atmA.out.utilMixture,
               init := atmA.out.initAfterDisposed,
               empty := empty,
               reagentValveClosed := reagentValveClosed );

    updateOutputs();
END


METHOD PRIVATE updateOutputs
BEGIN
    out.preparingReagentIndicator := atmA.out.preparingReagentIndicator;
    out.preparingMixtureIndicator := atmA.out.preparingMixtureIndicator;
    out.usingMixtureIndicator     := atmA.out.usingMixtureIndicator;
    out.interruptIndicator        := atmA.out.interruptIndicator;

    out.waterValve   := atmB.out.waterValve;
    out.mixtureValve := atmA.out.mixtureValve;
    out.mixer        := atmB.out.mixer;

    out.reagentValveOpen  := atmC.out.reagentValveOpen;
    out.reagentValveClose := atmC.out.reagentValveClose OR atmF.out.reagentValveClose;
    out.inletPump         := atmC.out.inletPump;
    out.outletPump        := atmA.out.outletPump OR atmF.out.outletPump;
END


TYPE OutputModel :
STRUCT
    preparingReagentIndicator: BOOL := FALSE;
    preparingMixtureIndicator: BOOL := FALSE;
    usingMixtureIndicator:     BOOL := FALSE;
    interruptIndicator:        BOOL := FALSE;
    waterValve:                BOOL := FALSE;
    mixtureValve:              BOOL := FALSE;
    mixer:                     BOOL := FALSE;
    reagentValveOpen:          BOOL := FALSE;
    reagentValveClose:         BOOL := FALSE;
    inletPump:                 BOOL := FALSE;
    outletPump:                BOOL := FALSE;
END_STRUCT
END_TYPE


METHOD PUBLIC getState : ModelState
BEGIN
    getState.stateA := atmA.getState();
    getState.stateB := atmB.getState();
    getState.stateC := atmC.getState();
    getState.stateD := atmD.getState();
    getState.stateE := atmE.getState();
    getState.stateF := atmF.getState();
END


TYPE ModelState :
STRUCT
    stateA: UINT;
    stateB: UINT;
    stateC: UINT;
    stateD: UINT;
    stateE: UINT;
    stateF: UINT;
END_STRUCT
END_TYPE


END_FUNCTION_BLOCK