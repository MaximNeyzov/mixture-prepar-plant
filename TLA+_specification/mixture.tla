------------------------------ MODULE mixture ------------------------------

EXTENDS Naturals

States == 1..6

VARIABLES
    (* Automata states *)
    stateA,
    stateB,
    stateC,
    stateD,
    stateE,
    stateF,
    (* Automata outputs *)
    outA,
    outB,
    outC,
    outD,
    outE,
    outF,
    (* Signal perspectives *)
    atmB_endPersp,
    atmC_endPersp,
    atmD_endPersp,
    atmE_reagentSpoiledPersp,
    (* Signal retrospectives *)
    atmE_waitingRetro,
    atmF_endRetro,
    (* Model inputs *)
    start,
    ackInterrupt,
    materialLoaded,
    concentratePoured,
    homogenComplete,
    violated,
    unstabilReagent,
    utilEnded,
    empty,
    high,
    full,
    reagentValveOpened,
    reagentValveClosed,
    (* Special model outputs -- outputs that combine several outputs of different automata *)
    reagentValveClose,
    outletPump,
    (* Recognition automata states *)
    pumpBuchiState,
    mixtureFeedBuchiState,
    (* Auxiliary variables *)
    outletPump_rise,
    _stateA, \* _stateA(t) = stateA(t-1)
    _stateB,
    _stateD,
    _stateE

vars == << stateA, stateB, stateC, stateD, stateE, stateF,
           outA, outB, outC, outD, outE, outF,
           atmB_endPersp, atmC_endPersp, atmD_endPersp, atmE_reagentSpoiledPersp,
           atmE_waitingRetro, atmF_endRetro,
           start, ackInterrupt, materialLoaded, concentratePoured, homogenComplete, violated, unstabilReagent, utilEnded, empty, high, full, reagentValveOpened, reagentValveClosed,
           reagentValveClose, outletPump,
           pumpBuchiState, mixtureFeedBuchiState, outletPump_rise, _stateA, _stateB, _stateD, _stateE >>

atmA == INSTANCE AutomatonA WITH state <- stateA, out <- outA
atmB == INSTANCE AutomatonB WITH state <- stateB, out <- outB
atmC == INSTANCE AutomatonC WITH state <- stateC, out <- outC
atmD == INSTANCE AutomatonD WITH state <- stateD, out <- outD
atmE == INSTANCE AutomatonE WITH state <- stateE, out <- outE
atmF == INSTANCE AutomatonF WITH state <- stateF, out <- outF

tank == INSTANCE Tank
reagentValve == INSTANCE ReagentValve WITH opened <- reagentValveOpened, closed <- reagentValveClosed

pumpBuchi == INSTANCE PumpBuchi WITH state <- pumpBuchiState
mixtureFeedBuchi == INSTANCE MixtureFeedBuchi WITH state <- mixtureFeedBuchiState

\***********************************************************************
Init ==
    /\ atmA!Init
    /\ atmB!Init
    /\ atmC!Init
    /\ atmD!Init
    /\ atmE!Init
    /\ atmF!Init
    /\ tank!Init
    /\ reagentValve!Init
    /\ pumpBuchi!Init
    /\ mixtureFeedBuchi!Init
    /\ atmB_endPersp = FALSE
    /\ atmC_endPersp = FALSE
    /\ atmD_endPersp = FALSE
    /\ atmE_reagentSpoiledPersp = FALSE
    /\ atmE_waitingRetro = TRUE
    /\ atmF_endRetro = FALSE
    /\ start = FALSE
    /\ ackInterrupt = FALSE
    /\ materialLoaded = FALSE
    /\ concentratePoured = FALSE
    /\ homogenComplete = FALSE
    /\ violated = FALSE
    /\ unstabilReagent = FALSE
    /\ utilEnded = FALSE
    /\ reagentValveClose = FALSE
    /\ outletPump = FALSE
    /\ outletPump_rise = FALSE
    /\ _stateA = stateA
    /\ _stateB = stateB
    /\ _stateD = stateD
    /\ _stateE = stateE

\***********************************************************************
\* "start" signal waiting
start_waiting == (stateA = 1)

define_start ==
    /\ start' \in BOOLEAN
    /\ start' => start_waiting

\***********************************************************************
\* "ackInterrupt" signal waiting
ackInterrupt_waiting == (stateA = 5 \/ stateA = 6)

define_ackInterrupt ==
    /\ ackInterrupt' \in BOOLEAN
    /\ ackInterrupt' => ackInterrupt_waiting

\***********************************************************************
\* "materialLoaded" signal waiting
materialLoaded_waiting == (stateD = 2)

define_materialLoaded ==
    /\ materialLoaded' \in BOOLEAN
    /\ materialLoaded' => materialLoaded_waiting

\***********************************************************************
\* "concentratePoured" signal waiting
concentratePoured_waiting == (stateD = 3)

define_concentratePoured ==
    /\ concentratePoured' \in BOOLEAN
    /\ concentratePoured' => concentratePoured_waiting

\***********************************************************************
\* "homogenComplete" signal waiting
homogenComplete_waiting == (stateD = 4)

define_homogenComplete ==
    /\ homogenComplete' \in BOOLEAN
    /\ homogenComplete' => homogenComplete_waiting

\***********************************************************************
\* "violated" signal waiting
violated_waiting == (stateE = 2)

define_violated ==
    /\ violated' \in BOOLEAN
    /\ violated' => violated_waiting

\***********************************************************************
\* "unstabilReagent" signal waiting
unstabilReagent_waiting == (stateE = 2)

define_unstabilReagent ==
    /\ unstabilReagent' \in BOOLEAN
    /\ unstabilReagent' => unstabilReagent_waiting

\***********************************************************************
\* "utilEnded" signal waiting
utilEnded_waiting == (stateE = 3)

define_utilEnded ==
    /\ utilEnded' \in BOOLEAN
    /\ utilEnded' => utilEnded_waiting

\***********************************************************************
define_levelSensors ==
    LET
        inlet ==
            \/ outB.waterValve
            \/ outC.inletPump /\ ~reagentValveClosed
        outlet == outletPump
    IN
    tank!iter(inlet, outlet)

\***********************************************************************
define_reagentValveSensors ==
    reagentValve!iter(outC.reagentValveOpen, reagentValveClose)

\***********************************************************************
define_inputs ==
    /\ define_start
    /\ define_ackInterrupt
    /\ define_materialLoaded
    /\ define_concentratePoured
    /\ define_homogenComplete
    /\ define_violated
    /\ define_unstabilReagent
    /\ define_utilEnded
    /\ define_levelSensors
    /\ define_reagentValveSensors

\***********************************************************************
retrospectives ==
    /\ atmE_waitingRetro' = outE.waiting
    /\ atmF_endRetro'     = outF.end

perspectives ==
    /\ atmC_endPersp' = atmC!getEndPerspective(FALSE, FALSE, FALSE, reagentValveOpened', reagentValveClosed', full')
    /\ atmB_endPersp' = atmB!getEndPerspective(FALSE, FALSE, high', atmC_endPersp')
    /\ atmE_reagentSpoiledPersp' = atmE!getReagentSpoiledPerspective(FALSE, atmB_endPersp', violated', unstabilReagent', utilEnded')
    /\ atmD_endPersp' = atmD!getEndPerspective(FALSE, materialLoaded', concentratePoured', homogenComplete', atmE_reagentSpoiledPersp') 

atm_iter ==
    /\ _stateA' = stateA
    /\ _stateB' = stateB
    /\ _stateD' = stateD
    /\ _stateE' = stateE
    /\ atmA!iter(start', atmE_waitingRetro', atmD_endPersp', atmB_endPersp', atmE_reagentSpoiledPersp', empty', ackInterrupt', atmF_endRetro')
    /\ atmD!iter(outA'.prepareReagent, materialLoaded', concentratePoured', homogenComplete', atmE_reagentSpoiledPersp')
    /\ atmE!iter(outD'.startReagentStabilization, atmB_endPersp', violated', unstabilReagent', utilEnded')
    /\ atmB!iter(outA'.prepareMixture, outA'.stopPrepareMixture, high', atmC_endPersp')
    /\ atmC!iter(outB'.reagentFeed, outE'.unstabilReagent, outB'.resetSlave, reagentValveOpened', reagentValveClosed', full')
    /\ atmF!iter(outA'.utilMixture, outA'.initAfterDisposed, empty', reagentValveClosed')

define_outputs ==
    /\ reagentValveClose' = (outC'.reagentValveClose \/ outF'.reagentValveClose)
    /\ outletPump'        = (outA'.outletPump \/ outF'.outletPump)
    /\ outletPump_rise'   = (~outletPump /\ outletPump')

propertyBuchi ==
    /\ pumpBuchi!iter(outC'.inletPump, full')
    /\ mixtureFeedBuchi!iter(full', empty', outE'.reagentSpoiled, outletPump', outletPump_rise', outA'.mixtureValve)

Next ==
    /\ define_inputs
    /\ retrospectives
    /\ perspectives
    /\ atm_iter
    /\ define_outputs
    /\ propertyBuchi

\***********************************************************************
Fairness ==
    LET
        inlet ==
            \/ outB.waterValve
            \/ outC.inletPump /\ ~reagentValveClosed
        outlet == outletPump
    IN
    /\ WF_vars(Next)
    /\ <>[](start_waiting)             => []<>(start)
    /\ <>[](ackInterrupt_waiting)      => []<>(ackInterrupt)
    /\ <>[](materialLoaded_waiting)    => []<>(materialLoaded)
    /\ <>[](concentratePoured_waiting) => []<>(concentratePoured)
    /\ <>[](homogenComplete_waiting)   => []<>(homogenComplete)
    /\ <>[](utilEnded_waiting)         => []<>(utilEnded)
    /\ []<>(outlet)                    => []<>(inlet  \/ empty)
    /\ []<>(inlet )                    => []<>(outlet \/ full )
    /\ []<>(outC.reagentValveOpen )    => []<>(     reagentValveClose \/ reagentValveOpened)
    /\ []<>(     reagentValveClose)    => []<>(outC.reagentValveOpen  \/ reagentValveClosed)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

\***********************************************************************
TypeInv ==
    /\ stateA \in States
    /\ stateB \in States
    /\ stateC \in States
    /\ stateD \in States
    /\ stateE \in States
    /\ stateF \in States
    /\ outA \in atmA!Output
    /\ outB \in atmB!Output
    /\ outC \in atmC!Output
    /\ outD \in atmD!Output
    /\ outE \in atmE!Output
    /\ outF \in atmF!Output

\***********************************************************************
(* Корректность команды закрытия клапана подачи реагента:
автоматы C и F не выдают команду на закрытие клапана одновременно *)
Inv1 == \* valid
    ~(outC.reagentValveClose /\ outF.reagentValveClose)

\***********************************************************************
(* Если клапан подачи воды открыт, то:
- клапан подачи реагента закрыт и не открывается;
- впускной насос отключён;
- выпускной насос отключён;
- смеситель отключён;
- клапан подачи смеси не активирован *)
Inv2 == \* valid
    outB.waterValve => /\ reagentValveClosed
                       /\ ~outC.reagentValveOpen
                       /\ ~outC.inletPump
                       /\ ~outletPump
                       /\ ~outB.mixer
                       /\ ~outA.mixtureValve

\***********************************************************************
(* Если клапан подачи реагента открывается или не закрыт, то клапан подачи воды закрыт *)
Inv3 == \* valid
    (outC.reagentValveOpen \/ ~reagentValveClosed) => ~outB.waterValve

\***********************************************************************
(* Если работает впускной насос, то:
- клапан подачи реагента открыт;
- клапан подачи воды закрыт;
- смеситель включен;
- выпускной насос отключён *)
Inv4 == \* valid
    outC.inletPump => /\ reagentValveOpened
                      /\ ~outB.waterValve
                      /\ outB.mixer
                      /\ ~outletPump

\***********************************************************************
(* Если работает выпускной насос, то:
- впускной насос отключён;
- клапан подачи воды закрыт;
- смеситель отключён *)
Inv5 == \* valid
    outletPump => /\ ~outC.inletPump
                  /\ ~outB.waterValve
                  /\ ~outB.mixer

\***********************************************************************
(* Если клапан подачи смеси активирован, то работает выпускной насос *)
Inv6 == \* valid
    outA.mixtureValve => outletPump

\***********************************************************************
(* Если в баке достигнут высокий уровень, то клапан подачи воды закрыт *)
Inv7 == \* valid
    high => ~outB.waterValve

\***********************************************************************
(* Если бак заполнен, то впускной насос отключён и клапан подачи воды закрыт *)
Inv8 == \* valid
    full => (~outC.inletPump /\ ~outB.waterValve)

\***********************************************************************
(* Если реагент испорчен, то всё оборудование отключено, кроме выпускного насоса *)
Inv9 == \* valid
    outE.reagentSpoiled =>
        /\ ~outA.mixtureValve
        /\ ~outB.waterValve
        /\ ~outB.mixer
        /\ ~outC.inletPump
        /\ ~outC.reagentValveOpen
        /\ ~reagentValveClose

\***********************************************************************
(* Если реагент нестабилен, то впускной насос отключён *)
Inv10 == \* valid
    unstabilReagent => ~outC.inletPump

\***********************************************************************
(* Если реагент испорчен и бак не пуст, то работает выпускной насос и клапан подаёт смесь в дренаж *)
Inv11 == \* valid
    (outE.reagentSpoiled /\ ~empty) => (outletPump /\ ~outA.mixtureValve)

\***********************************************************************
(* Если работает выпускной насос и клапан подаёт смесь потребителю,
   то тех. процесс находится на стадии использования смеси *)
Inv12 == \* valid
    (outletPump /\ outA.mixtureValve) => (stateA = 4)

\***********************************************************************
(* Если приготовление смеси прервано (из-за испорченного реагента),
   то впускной насос отключён и клапан подачи воды закрыт *)
Inv13 == \* valid
    (stateA = 6) => (~outC.inletPump /\ ~outB.waterValve)


\***********************************************************************
(* При отсутствии нарушений все команды для оборудования будут задействованы *)
Prop1 == \* valid
    [](~violated) =>
        /\ <>(outletPump)
        /\ <>(outB.waterValve)
        /\ <>(outB.mixer)
        /\ <>(outC.inletPump)
        /\ <>(outC.reagentValveOpen)
        /\ <>(outC.reagentValveClose)

\***********************************************************************
(* При отсутствии нарушений всегда в будущем бак будет заполняться и опустошаться *)
Prop2 == \* valid
    [](~violated) => /\ []<>( full)
                     /\ []<>(empty)

\***********************************************************************
(* При отсутствии нарушений всегда в будущем смесь будет подаваться потребителю *)
Prop3 == \* valid
    [](~violated) => /\ []<>(stateA = 4)
                     /\ []<>(stateA # 4)

\***********************************************************************
(* Непрерывность работы впускного насоса:
если впускной насос включился, то будет работать до тех пор, пока не наполнится бак.
LTL: G(inletPump -> inletPump U full).
Модуль pumpBuchi - автомат-распознаватель LTL-свойства.
Свойство выполняется, если автомат Бюхи бесконечно часто проходит через состояние 0.
Необходимые условия для непрерывной работы насоса: нет нарушений и всегда стабильный реагент.
*)
Prop4 == \* valid
    [](~violated /\ ~unstabilReagent) =>
        []<>(pumpBuchiState = 0)

\***********************************************************************
(* При отсутствии нарушений,
если клапан подачи реагента не перемещается (открывается/закрывается),
то он находится в одном из крайних положений *)
Prop5 == \* valid
    [](~violated) =>
        ( ~(outC.reagentValveOpen \/ reagentValveClose) => (reagentValveOpened \/ reagentValveClosed) )

\***********************************************************************
(* Конечное время работы устройств:
   если устройство включилось, то в будущем оно обязательно отключится *)
Prop6 == \* valid
    /\ []( outletPump            => <>(~outletPump)            )
    /\ []( outA.mixtureValve     => <>(~outA.mixtureValve)     )
    /\ []( outB.waterValve       => <>(~outB.waterValve)       )
    /\ []( outB.mixer            => <>(~outB.mixer)            )
    /\ []( outC.inletPump        => <>(~outC.inletPump)        )
    /\ []( outC.reagentValveOpen => <>(~outC.reagentValveOpen) )
    /\ []( reagentValveClose     => <>(~reagentValveClose)     )

\***********************************************************************
(* Подача потребителю нормальной смеси:
всегда, если бак заполнен, реагент не испорчен и включился выпускной насос, то он будет работать вместе с клапаном подачи смеси потребителю до тех пор, пока не опустошится бак.
LTL: G( full & !reagentSpoiled & outletPump_rise -> (outletPump & mixtureValve U empty) ).
outletPump_rise - передний фронт сигнала outletPump.
Модуль mixtureFeedBuchi - автомат-распознаватель LTL-свойства.
Свойство выполняется, если автомат Бюхи бесконечно часто проходит через состояние 0.
*)
Prop7 == \* valid
    []<>(mixtureFeedBuchiState = 0)

\***********************************************************************
\* Внутренние требования к реакциям модели управления (t1..t6)
\* Проверка безынерционности модели
\***********************************************************************
(* Requirement t1 *)
t1 == \* valid
    (_stateA = 2 /\ homogenComplete) => (stateA = 3 \/ violated)

\***********************************************************************
(* Requirement t2 *)
t2 == \* valid
    (_stateA = 2 /\ _stateD = 4 /\ violated) => (stateA = 5 /\ stateD = 1)

\***********************************************************************
(* Requirement t3 *)
t3 == \* valid
    (_stateA = 3 /\ violated) => ((stateA = 6 /\ stateB = 1 /\ stateC = 1) \/ outB.end)

\***********************************************************************
(* Requirement t4 *)
t4 == \* valid
    (_stateA = 3 /\ outB.end) => (stateA = 4)

\***********************************************************************
(* Requirement t5 *)
t5 == \* valid
    (_stateE = 2 /\ outB.end) => (stateE = 3)

\***********************************************************************
(* Requirement t6 *)
t6 == \* valid
    (_stateB = 3 /\ outC.end) => outB.end


\***********************************************************************
\* Проверка согласованности сигналов и их перспектив.
\***********************************************************************
atmB_endPerspConform == \* valid
    (~outA.stopPrepareMixture => atmB_endPersp = outB.end)

atmC_endPerspConform == \* valid
    (~outA.stopPrepareMixture => atmC_endPersp = outC.end)

reagentSpoiledPerspConform == \* valid
    (atmE_reagentSpoiledPersp = outE.reagentSpoiled)

atmD_endPerspConform == \* valid
    (atmD_endPersp = outD.end)


=============================================================================
