import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.ATP.DifferentiableATP.TacticDecoder
import HeytingLean.ATP.DifferentiableATP.ConvergenceOracle
import HeytingLean.ATP.DifferentiableATP.CoreOps
import HeytingLean.ATP.DifferentiableATP.RetractedGD
import HeytingLean.ATP.DifferentiableATP.TypeLoss
import HeytingLean.ATP.DifferentiableATP.GradientProbe
import HeytingLean.ATP.DifferentiableATP.CategoricalBridge
import HeytingLean.ATP.DifferentiableATP.MultiwayGD
import HeytingLean.ATP.DifferentiableATP.KANTacticSelector
import HeytingLean.ATP.DifferentiableATP.GraphNCA
import HeytingLean.ATP.DifferentiableATP.KANNCA
import HeytingLean.ATP.DifferentiableATP.ProgressEstimator
import HeytingLean.ATP.DifferentiableATP.SheafResolution
import HeytingLean.ATP.DifferentiableATP.SheafTransport
import HeytingLean.ATP.FreeEnergySearch
import HeytingLean.Embeddings.CrossLensTransport

/-!
# ATP.DifferentiableATP.LensGDOrchestrator

Multi-lens differentiable optimization loop:
embed -> projected GD -> convergence check -> optional lane change.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.Embeddings
open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

private def clamp01 (r : Rat) : Rat :=
  if r < 0 then 0 else if r > 1 then 1 else r

private def gradientDescentLoopWith
    (stepFn : GDConfig → List IOExample → FSum → FSum)
    (config : GDConfig)
    (typeCfg : TypeLossConfig)
    (examples : List IOExample)
    (initial : FSum) : Compute.GDState :=
  let rec go : Nat → Nat → FSum → Option FSum → List Rat → Compute.GDState
    | 0, iter, w, prev, hist =>
        let lIO := Compute.totalLoss config.regularization w examples
        let l := combinedLossV2 typeCfg nucleusR lIO w prev iter
        { iteration := iter, currentWeights := w, currentLoss := l, lossHistory := hist.reverse }
    | Nat.succ fuel, iter, w, prev, hist =>
        let lIO := Compute.totalLoss config.regularization w examples
        let l := combinedLossV2 typeCfg nucleusR lIO w prev iter
        let w' := stepFn config examples w
        go fuel (iter + 1) w' (some w) (l :: hist)
  go config.iterations 0 (projectToFixedWeights nucleusR initial) none []

def gradientDescentLoopProjected
    (config : GDConfig)
    (typeCfg : TypeLossConfig)
    (examples : List IOExample)
    (initial : FSum) : Compute.GDState :=
  gradientDescentLoopWith gradientStepProjected config typeCfg examples initial

def gradientDescentLoopRetracted
    (config : GDConfig)
    (typeCfg : TypeLossConfig)
    (examples : List IOExample)
    (initial : FSum) : Compute.GDState :=
  gradientDescentLoopWith retractedGradientStep config typeCfg examples initial

inductive GDMode where
  | projected
  | retracted
  deriving Repr, DecidableEq

inductive TrackMode where
  | baseline
  | kan
  | nca
  | kan_nca
  deriving Repr, DecidableEq

structure OrchestratorConfig where
  currentLens : LensID := .omega
  maxIterations : Nat := 24
  maxLaneChanges : Nat := 2
  lensBudget : Nat := 3
  regularization : Rat := 0
  decodeTopK : Nat := 4
  usePremiseHints : Bool := true
  attentionTopK : Nat := 5
  premiseHintBudget : Nat := 4
  typeLossConfig : TypeLossConfig := {}
  gdMode : GDMode := .retracted
  useMultiwayGD : Bool := false
  softKernelDepth : Nat := 3
  stepFuel : Nat := 1
  simplicityWeight : Rat := (1 : Rat) / 100
  useReachLoss : Bool := false
  reachFuel : Nat := 2
  reachWeight : Rat := (1 : Rat) / 10
  maxMacroSteps : Nat := 5
  innerIterations : Nat := 20
  lockTopK : Nat := 6
  exactGradient : Bool := true
  useLearnedTactics : Bool := false
  useKANSelector : Bool := false
  useOracleEncoding : Bool := false
  oracleExamples : Option (List IOExample) := none
  trackMode : TrackMode := .baseline
  ncaMaxSteps : Nat := 12
  ncaTolerance : Rat := (1 : Rat) / 1000
  ncaPerturbStep : Nat := 0
  ncaPerturbDrop : Rat := 0
  ncaPerturbSeed : Nat := 0
  enableTrackTraining : Bool := false
  trackTrainingIterations : Nat := 12
  trackTrainingLearningRate : Rat := (1 : Rat) / 100
  trackTrainingSampleBudget : Nat := 9
  trackTrainingParamBudget : Nat := 10
  trackTrainingLossSteps : Nat := 8
  trainingSamples : List (String × String) := []
  enrichedTrainingSamples : List EnrichedTrainingSample := []
  enableTacticDiversification : Bool := true
  diversityTopK : Nat := 4
  preferredTactic : Option String := none
  useStructuralInjection : Bool := true
  structuralInjectionBudget : Nat := 3
  subgoalCloserBudget : Nat := 5
  compoundCloserBudget : Nat := 12
  useGradientSelection : Bool := true
  useSheafTransport : Bool := true
  emitGDTrace : Bool := false
  probeConfig : ProbeConfig := {}
  oracle : ConvergenceOracle.Config := {}

structure CategoricalEvidence where
  algebraHomWitness : Bool
  stepPreservesEvidence : Bool
  mapFixedUsed : Bool
  witnessTheorems : List String
  transportMode : String
  deriving Repr

structure LaneSegment where
  lens : LensID
  encoded : EncodedGoal
  state : Compute.GDState
  verdict : ConvergenceOracle.Verdict
  psrLoss : Rat
  dialecticLoss : Rat
  occamLoss : Rat
  psrDynamicsLoss : Rat
  curriculumWeight : Rat
  sheafResolution : Nat
  sheafBasisSize : Nat
  attentionKeywords : List String
  premiseHintsUsed : List String
  gradientProbes : List ProbeResult
  candidates : List DecodedCandidate
  multiwayMode : Bool
  trackMode : TrackMode
  trackConverged : Bool
  trackCellCount : Nat
  trackStabilityScore : Rat
  symbolicSummaries : List String
  progressScore : Rat
  tacticDiversityIndex : Rat
  laneDecision : LaneDecision

structure Result where
  ok : Bool
  goal : String
  segments : List LaneSegment
  laneHistory : List LensID
  laneChangesUsed : Nat
  finalLens : LensID
  bestWeights : FSum
  bestCandidates : List DecodedCandidate
  psrLoss : Rat
  dialecticLoss : Rat
  occamLoss : Rat
  psrDynamicsLoss : Rat
  psrConverged : Bool
  monotonicityScore : Rat
  sheafFinalResolution : Nat
  sheafFinalBasisSize : Nat
  attentionKeywords : List String
  premiseHintsUsed : List String
  gdMode : GDMode
  trackMode : TrackMode
  trackConverged : Bool
  trackCellCount : Nat
  trackStabilityScore : Rat
  symbolicSummaries : List String
  progressScore : Rat
  tacticDiversityIndex : Rat
  categoricalEvidence : CategoricalEvidence
  useSheafTransport : Bool
  useMultiwayGD : Bool
  reason : String
  transportUsed : Bool

private def gdConfigOf (cfg : OrchestratorConfig) (basis : List Comb) : GDConfig :=
  {
    learningRate := (1 : Rat) / 5
    iterations := max 1 cfg.maxIterations
    regularization := cfg.regularization
    params := if basis.isEmpty then [.K, .S, .Y] else basis
  }

private def macroConfigOf (cfg : OrchestratorConfig) (gdCfg : GDConfig) : MacroConfig :=
  {
    maxMacroSteps := max 1 cfg.maxMacroSteps
    innerIterations := max 1 cfg.innerIterations
    lockTopK := max 1 cfg.lockTopK
    simplifyDepth := 3
    stepFuel := max 1 cfg.stepFuel
    softKernelDepth := max 1 cfg.softKernelDepth
    learningRate := gdCfg.learningRate
    simplicityWeight := cfg.simplicityWeight
    tacticScoreWeight := if cfg.useLearnedTactics then (1 : Rat) / 50 else 0
    tacticTopK := max 1 cfg.decodeTopK
    convergenceThreshold := (1 : Rat) / 100
    exactGradient := cfg.exactGradient
    useLearnedTactics := cfg.useLearnedTactics
    useReachLoss := cfg.useReachLoss
    reachFuel := max 1 cfg.reachFuel
    reachWeight := cfg.reachWeight
  }

private def chooseBestSegment? : List LaneSegment → Option LaneSegment
  | [] => none
  | s :: rest =>
      some <| rest.foldl
        (fun best row =>
          if row.state.currentLoss < best.state.currentLoss then row else best)
        s

private def beliefsFrom (pos : ProofPosition) (isStuckHere : Bool) : ProofBeliefs :=
  {
    stuckProbability := fun lens =>
      if lens = pos.lens then
        if isStuckHere then 5 else 1
      else
        1
  }

private def probeModeOf : GDMode → ProbeGDMode
  | .projected => .projected
  | .retracted => .retracted

private def ncaPerturbConfigOf (cfg : OrchestratorConfig) : Option NCAPerturbConfig :=
  if cfg.ncaPerturbStep = 0 || cfg.ncaPerturbDrop <= 0 then
    none
  else
    some
      {
        step := cfg.ncaPerturbStep - 1
        dropAlive := cfg.ncaPerturbDrop
        seed := cfg.ncaPerturbSeed
      }

private def usageTrackerOf (rows : List DecodedCandidate) : TacticUsageTracker :=
  rows.foldl (fun t row => t.bump row.tactic) {}

private def injectPreferred (preferred : String) : Option DecodedCandidate :=
  match tacticTable.find? (fun row => row.tactic = preferred) with
  | some row =>
      some
        {
          comb := row.pattern
          tactic := row.tactic
          source := s!"preferred::{row.family}"
          confidence := 2
        }
  | none => none

private def preferTactic (preferred : Option String) (rows : List DecodedCandidate) : List DecodedCandidate :=
  match preferred with
  | none => rows
  | some tactic =>
      match rows.find? (fun r => r.tactic = tactic) with
      | some hit => hit :: rows.filter (fun r => r.tactic ≠ tactic)
      | none =>
          match injectPreferred tactic with
          | some injected => injected :: rows
          | none => rows

private def mergeUniqueCandidates
    (primary secondary : List DecodedCandidate) : List DecodedCandidate :=
  primary ++ secondary.filter (fun row => !(primary.any (fun p => p.tactic = row.tactic)))

private def dedupCandidatesByTactic (rows : List DecodedCandidate) : List DecodedCandidate :=
  rows.foldl
    (fun acc row =>
      if acc.any (fun x => x.tactic = row.tactic) then acc else acc ++ [row])
    []

def mkInjectedCandidate
    (tactic : String)
    (source : String)
    (confidence : Rat := (1 : Rat) / 10) : DecodedCandidate :=
  match tacticTable.find? (fun row => row.tactic = tactic) with
  | some row =>
      {
        comb := row.pattern
        tactic := row.tactic
        source := source
        confidence := confidence
      }
  | none =>
      {
        comb := .K
        tactic := tactic
        source := source
        confidence := confidence
      }

private def freshInjected
    (existing : List DecodedCandidate)
    (tactics : List String)
    (sourcePrefix : String)
    (budget : Nat) : List DecodedCandidate :=
  let k := max 1 budget
  let injected :=
    tactics.filterMap (fun tactic =>
      if existing.any (fun row => row.tactic = tactic) then
        none
      else
        some (mkInjectedCandidate tactic s!"{sourcePrefix}::{tactic}"))
  injected.take k

private def interleaveCandidates
    (primary injected : List DecodedCandidate) : List DecodedCandidate :=
  match primary, injected with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => x :: y :: interleaveCandidates xs ys

private def structuralInjectionTactics (goal : String) : List String :=
  let f := goalFeatures goal
  let rows0 : List String := if f.hasAnd || f.hasIff then ["constructor", "apply And.intro"] else []
  let rows1 : List String := if f.hasForall || f.hasExists then rows0 ++ ["intro", "intros"] else rows0
  let rows2 : List String := if f.hasOr then rows1 ++ ["cases"] else rows1
  let hasNatOrList := f.hasNat || f.hasList
  let rows3 : List String :=
    if hasNatOrList && f.hasForall then
      rows2 ++
      [ "intro n; induction n with | zero => simp | succ k ih => simp_all"
      , "intro n; induction n with | zero => simp | succ k ih => simp_all; omega"
      , "intro n; cases n with | zero => simp | succ k => simp_all"
      , "intro l; induction l with | nil => simp | cons h t ih => simp_all"
      , "intro l; induction l with | nil => simp | cons h t ih => simp_all; omega"
      , "intro l; cases l with | nil => simp | cons h t => simp"
      ]
    else
      rows2
  rows3.eraseDups

def closerInjectionTactics (goal : String) : List String :=
  let f := goalFeatures goal
  let hasArithmetic := f.hasNat || f.hasInt || f.hasReal || f.hasPlus || f.hasMul || f.hasLt || f.hasLe
  let hasLogic := f.hasArrow || f.hasIff || f.hasAnd || f.hasOr || f.hasNot
  let arithClosers := if hasArithmetic then ["omega", "linarith", "nlinarith", "ring", "norm_num"] else []
  let logicClosers := if hasLogic then ["tauto", "aesop", "decide"] else []
  (arithClosers ++ logicClosers ++ ["simp"]).eraseDups

def compoundCloserInjectionTactics (goal : String) : List String :=
  let f := goalFeatures goal
  let hasArithmetic := f.hasNat || f.hasInt || f.hasReal || f.hasPlus || f.hasMul || f.hasLt || f.hasLe
  let hasLogic := f.hasArrow || f.hasIff || f.hasAnd || f.hasOr || f.hasNot
  let hasQuantifier := f.hasForall || f.hasExists
  let hasEquality := f.hasEq
  let introChains :=
    if hasQuantifier then
      let introsArith :=
        if hasArithmetic then ["intros; omega", "intros; linarith", "intros; nlinarith", "intros; norm_num"] else []
      let introsRing :=
        if hasEquality && (f.hasMul || f.hasPlus) then ["intros; ring"] else []
      let introsLogic := if hasLogic then ["intros; tauto", "intros; simp"] else []
      let introArith :=
        if hasArithmetic then ["intro; omega", "intro; linarith", "intro; nlinarith", "intro; norm_num"] else []
      let introRing :=
        if hasEquality && (f.hasMul || f.hasPlus) then ["intro; ring"] else []
      let introLogic := if hasLogic then ["intro; tauto", "intro; simp"] else []
      introsArith ++ introsRing ++ introsLogic ++ introArith ++ introRing ++ introLogic
    else []
  let combinatorChains :=
    if f.hasAnd then
      let arithAll :=
        if hasArithmetic then
          ["constructor <;> omega", "constructor <;> linarith", "constructor <;> norm_num"]
        else []
      let logicAll := if hasLogic then ["constructor <;> tauto", "constructor <;> simp"] else []
      let ringAll :=
        if hasEquality && (f.hasMul || f.hasPlus) then ["constructor <;> ring"] else []
      arithAll ++ logicAll ++ ringAll
    else []
  let nestedSplits :=
    if f.hasAnd then
      ["constructor; constructor; omega", "constructor; constructor; tauto", "constructor; constructor; simp"]
    else []
  let ordered :=
    if f.hasAnd then
      combinatorChains ++ introChains ++ nestedSplits
    else
      introChains ++ combinatorChains ++ nestedSplits
  ordered.eraseDups

def universalConjunctionSolverTactics (goal : String) : List String :=
  let f := goalFeatures goal
  if !f.hasAnd then
    []
  else
    let closerList := String.intercalate " | "
      [ "omega", "tauto", "linarith", "nlinarith", "ring", "norm_num", "simp", "trivial"
      , "(intros; omega)", "(intros; tauto)", "(intros; ring)"
      , "(intros; linarith)", "(intros; nlinarith)", "(intros; norm_num)", "(intros; simp)"
      ]
    let universal := s!"repeat' constructor; all_goals first | {closerList}"
    let universalAlt := s!"repeat' (first | constructor | intro); first | {closerList}"
    [universal, universalAlt]

private def applyCandidateInjection
    (cfg : OrchestratorConfig)
    (goal : String)
    (rows : List DecodedCandidate) : List DecodedCandidate :=
  if !cfg.useStructuralInjection then
    rows
  else
    let structural :=
      freshInjected
        rows
        (structuralInjectionTactics goal)
        "structural_inject"
        (max 1 cfg.structuralInjectionBudget)
    let interleaved := interleaveCandidates rows structural
    let withClosers :=
      let closerRows :=
        freshInjected
          interleaved
          (closerInjectionTactics goal)
          "closer_inject"
          (max 1 cfg.subgoalCloserBudget)
      if closerRows.isEmpty then
        interleaved
      else
        interleaveCandidates interleaved closerRows
    let compoundRows :=
      freshInjected
        withClosers
        (compoundCloserInjectionTactics goal)
        "compound_closer_inject"
        (max 1 cfg.compoundCloserBudget)
    let withCompound :=
      if compoundRows.isEmpty then
        withClosers
      else
        interleaveCandidates withClosers compoundRows
    let universalRows :=
      freshInjected
        withCompound
        (universalConjunctionSolverTactics goal)
        "universal_solver_inject"
        2
    let withUniversal :=
      if universalRows.isEmpty then
        withCompound
      else
        interleaveCandidates withCompound universalRows
    dedupCandidatesByTactic withUniversal

private def formatTrainLoss (label : String) (r : Rat) : String :=
  let raw := toString r
  let compact := if raw.length > 96 then raw.take 96 ++ "..." else raw
  s!"{label}={compact}"

private def fmtRatShort (r : Rat) : String :=
  let s := toString r
  if s.length > 32 then s.take 32 ++ "…" else s

private def formatTraceEntry (pfx : String) (e : TrainingTraceEntry) : String :=
  let gradSum := e.gradNorms.foldl (fun acc g => acc + absRat g) 0
  let gradMax := e.gradNorms.foldl (fun acc g => max acc (absRat g)) 0
  let nZero := e.gradNorms.foldl (fun acc g => if g = 0 then acc + 1 else acc) (0 : Nat)
  let paramDelta := (List.range (min e.paramsBefore.size e.paramsAfter.size)).foldl
    (fun acc i => acc + absRat (e.paramsAfter.getD i 0 - e.paramsBefore.getD i 0)) 0
  s!"{pfx}_iter={e.iteration} loss={fmtRatShort e.lossBefore} grad_l1={fmtRatShort gradSum} grad_max={fmtRatShort gradMax} zero_grads={nZero}/{e.gradNorms.size} param_delta={fmtRatShort paramDelta}"

private def formatTrace (pfx : String) (trace : List TrainingTraceEntry) : List String :=
  trace.map (formatTraceEntry pfx)

private def trackModeCandidates
    (cfg : OrchestratorConfig)
    (encoded : EncodedGoal)
    (weights : FSum)
    (verdict : ConvergenceOracle.Verdict)
    (premiseHints : List String) :
    List DecodedCandidate × Bool × Nat × Rat × List String :=
  let goalFeat := kanGoalFeatures encoded.normalizedGoal
  let perturbCfg := ncaPerturbConfigOf cfg
  let (candidatesRaw, trackConverged, trackCellCount, trackStabilityScore, symbolicSummaries) :=
    match cfg.trackMode with
  | .baseline =>
      let candidates :=
        if cfg.useMultiwayGD then
          extractTacticCandidates (max 1 cfg.decodeTopK) weights
        else if cfg.useKANSelector then
          let selector :=
            if cfg.enableTrackTraining &&
               (!cfg.trainingSamples.isEmpty || !cfg.enrichedTrainingSamples.isEmpty) then
              let (trained, _, _) :=
                trainKANOnGoals
                  cfg.trainingSamples
                  warmStartSelector
                  (max 1 cfg.trackTrainingIterations)
                  cfg.trackTrainingLearningRate
                  ((1 : Rat) / 1000)
                  (max 1 cfg.trackTrainingSampleBudget)
                  (max 1 cfg.trackTrainingParamBudget)
                  (enrichedSamples := cfg.enrichedTrainingSamples)
              trained
            else
              warmStartSelector
          decodeFromKANWeightsWithGoalAndCompositions
            weights
            encoded.normalizedGoal
            (max 1 cfg.decodeTopK)
            6
            selector
        else if cfg.useLearnedTactics then
          decodeFromLearnedWeightsWithPremises
            weights
            premiseHints
            (max 1 cfg.decodeTopK)
            (max 1 cfg.premiseHintBudget)
            (max 1 cfg.softKernelDepth)
        else
          decodeFromWeightsWithPremisesAndTemperature
            verdict.temperature
            weights
            premiseHints
            (max 1 cfg.decodeTopK)
            (max 1 cfg.premiseHintBudget)
      (candidates, true, 0, 1, [])
  | .kan =>
      let trainingEnabled :=
        cfg.enableTrackTraining &&
        (!cfg.trainingSamples.isEmpty || !cfg.enrichedTrainingSamples.isEmpty)
      let (selector, maybeLoss, kanTrace) :=
        if trainingEnabled then
          let (trained, loss, trace) :=
            trainKANOnGoals
              cfg.trainingSamples
              warmStartSelector
              (max 1 cfg.trackTrainingIterations)
              cfg.trackTrainingLearningRate
              ((1 : Rat) / 1000)
              (max 1 cfg.trackTrainingSampleBudget)
              (max 1 cfg.trackTrainingParamBudget)
              (enrichedSamples := cfg.enrichedTrainingSamples)
          (trained, some loss, trace)
        else
          (warmStartSelector, none, [])
      let trainedCandidates :=
        decodeFromKANWeightsWithGoal
          weights
          encoded.normalizedGoal
          (max 1 cfg.decodeTopK)
          selector
      let baselineCandidates :=
        decodeFromKANWeightsWithGoal
          weights
          encoded.normalizedGoal
          (max 1 cfg.decodeTopK)
          warmStartSelector
      let candidates :=
        if trainingEnabled then
          -- Keep trained ordering authoritative while preserving baseline-only fallbacks.
          mergeUniqueCandidates trainedCandidates baselineCandidates
        else
          trainedCandidates
      let symbolicBase := kanSymbolicSummaries selector 8
      let traceSymbolic := if cfg.emitGDTrace then formatTrace "kan" kanTrace else []
      let symbolic :=
        match maybeLoss with
        | some l => (formatTrainLoss "kan_train_loss" l) :: symbolicBase ++ traceSymbolic
        | none => symbolicBase ++ traceSymbolic
      (candidates, true, 0, 1, symbolic)
  | .nca =>
      if cfg.enableTrackTraining && !cfg.trainingSamples.isEmpty then
        let (trainedRule, trainLoss, ncaTrace) :=
          trainNCARule
            cfg.trainingSamples
            defaultLearnableNCAUpdateRule
            (max 1 cfg.trackTrainingIterations)
            cfg.trackTrainingLearningRate
            ((1 : Rat) / 1000)
            (max 1 cfg.trackTrainingSampleBudget)
            (max 1 cfg.trackTrainingParamBudget)
            (max 1 cfg.trackTrainingLossSteps)
        let outcome :=
          runLearnableNCA
            { trainedRule with base := { trainedRule.base with maxCells := 64 } }
            weights
            (max 1 cfg.ncaMaxSteps)
            cfg.ncaTolerance
            goalFeat
            perturbCfg
        let baselineOutcome :=
          runNCA
            { defaultNCAUpdateRule with maxCells := 64 }
            weights
            (max 1 cfg.ncaMaxSteps)
            cfg.ncaTolerance
            goalFeat
            perturbCfg
        let candidates := mergeUniqueCandidates baselineOutcome.candidates outcome.candidates
        let traceSymbolic := if cfg.emitGDTrace then formatTrace "nca" ncaTrace else []
        ( candidates
        , outcome.converged
        , outcome.finalState.cells.length
        , outcome.stabilityScore
        , [formatTrainLoss "nca_train_loss" trainLoss] ++ traceSymbolic)
      else
        let outcome :=
          runNCA
            { defaultNCAUpdateRule with maxCells := 64 }
            weights
            (max 1 cfg.ncaMaxSteps)
            cfg.ncaTolerance
            goalFeat
            perturbCfg
        ( outcome.candidates
        , outcome.converged
        , outcome.finalState.cells.length
        , outcome.stabilityScore
        , [])
  | .kan_nca =>
      if cfg.enableTrackTraining &&
         (!cfg.trainingSamples.isEmpty || !cfg.enrichedTrainingSamples.isEmpty) then
        let (trainedSelector, kanLoss, kanTrace) :=
          trainKANOnGoals
            cfg.trainingSamples
            warmStartSelector
            (max 1 cfg.trackTrainingIterations)
            cfg.trackTrainingLearningRate
            ((1 : Rat) / 1000)
            (max 1 cfg.trackTrainingSampleBudget)
            (max 1 cfg.trackTrainingParamBudget)
            (enrichedSamples := cfg.enrichedTrainingSamples)
        let (trainedRule, ncaLoss, ncaTrace) :=
          trainNCARule
            cfg.trainingSamples
            defaultLearnableNCAUpdateRule
            (max 1 cfg.trackTrainingIterations)
            cfg.trackTrainingLearningRate
            ((1 : Rat) / 1000)
            (max 1 cfg.trackTrainingSampleBudget)
            (max 1 cfg.trackTrainingParamBudget)
            (max 1 cfg.trackTrainingLossSteps)
        let preNCA :=
          runLearnableNCA
            { trainedRule with base := { trainedRule.base with maxCells := 64 } }
            weights
            (max 1 cfg.ncaMaxSteps)
            cfg.ncaTolerance
            goalFeat
            perturbCfg
        let outcome :=
          runKANNCA
            {
              selector := trainedSelector
              ncaRule := { trainedRule.base with maxCells := 64 }
              maxSteps := max 1 cfg.ncaMaxSteps
              tolerance := cfg.ncaTolerance
              perturb := perturbCfg
            }
            (stateToFSum preNCA.finalState)
            goalFeat
        let baselineOutcome :=
          runKANNCA
            {
              selector := warmStartSelector
              ncaRule := { defaultNCAUpdateRule with maxCells := 64 }
              maxSteps := max 1 cfg.ncaMaxSteps
              tolerance := cfg.ncaTolerance
              perturb := perturbCfg
            }
            weights
            goalFeat
        let candidates := mergeUniqueCandidates baselineOutcome.candidates outcome.candidates
        let traceSymbolic := if cfg.emitGDTrace then formatTrace "kan" kanTrace ++ formatTrace "nca" ncaTrace else []
        ( candidates
        , outcome.converged
        , outcome.finalState.cells.length
        , outcome.stabilityScore
        , [formatTrainLoss "kan_train_loss" kanLoss, formatTrainLoss "nca_train_loss" ncaLoss] ++ outcome.symbolicSummaries ++ traceSymbolic)
      else
        let outcome :=
          runKANNCA
            {
              selector := warmStartSelector
              ncaRule := { defaultNCAUpdateRule with maxCells := 64 }
              maxSteps := max 1 cfg.ncaMaxSteps
              tolerance := cfg.ncaTolerance
              perturb := perturbCfg
            }
            weights
            goalFeat
        ( outcome.candidates
        , outcome.converged
        , outcome.finalState.cells.length
        , outcome.stabilityScore
        , outcome.symbolicSummaries)
  let candidates := applyCandidateInjection cfg encoded.normalizedGoal candidatesRaw
  (candidates, trackConverged, trackCellCount, trackStabilityScore, symbolicSummaries)

private def runSingleLane
    (cfg : OrchestratorConfig)
    (goal : String)
    (lens : LensID)
    (carry : Option FSum)
    (contextHints : List String) : LaneSegment :=
  let encoded := encodeGoal goal lens contextHints
    (if cfg.useOracleEncoding then cfg.oracleExamples else none)
  let lensBasis := basisForLens lens
  let alignedBasis :=
    let b := (encoded.basis.filter (fun c => c ∈ lensBasis)).eraseDups
    if b.isEmpty then lensBasis else b
  let initialRaw :=
    match carry with
    | some w => add encoded.initial w
    | none => encoded.initial
  let initial := lensRetractWeights lens initialRaw
  let gdCfg := gdConfigOf cfg alignedBasis
  let macroCfg := macroConfigOf cfg gdCfg
  let st :=
    if cfg.useMultiwayGD then
      let macroResult := multiwayMacroLoop macroCfg gdCfg.params initial encoded.examples
      {
        iteration := macroResult.macroStep * macroCfg.innerIterations
        currentWeights := macroResult.currentState
        currentLoss := macroResult.lossHistory.head?.getD 0
        lossHistory := macroResult.lossHistory.reverse
      }
    else
      match cfg.gdMode with
      | .projected => gradientDescentLoopProjected gdCfg cfg.typeLossConfig encoded.examples initial
      | .retracted => gradientDescentLoopRetracted gdCfg cfg.typeLossConfig encoded.examples initial
  let psrNow := psrLoss nucleusR st.currentWeights
  let dialNow :=
    match carry with
    | some prev => dialecticLoss nucleusR prev st.currentWeights
    | none => 0
  let occamNow := occamLoss st.currentWeights
  let dynNow :=
    match carry with
    | some _ => psrDynamicsLoss nucleusR st.currentWeights
    | none => 0
  let currNow := curriculumWeight cfg.typeLossConfig.curriculum st.iteration
  let verdict := ConvergenceOracle.evaluate { cfg.oracle with maxIterations := max 1 cfg.maxIterations } st psrNow dialNow
  let attentionKeywords := topKeywords st.currentWeights (max 1 cfg.attentionTopK)
  let premiseHints :=
    if cfg.usePremiseHints then
      (encoded.contextHints ++ attentionKeywords).eraseDups.take (max 1 cfg.premiseHintBudget)
    else
      []
  let (candidates, trackConverged, trackCellCount, trackStabilityScore, symbolicSummariesRaw) :=
    trackModeCandidates cfg encoded st.currentWeights verdict premiseHints
  let gdTraceSymbolic :=
    if cfg.emitGDTrace then
      let lossEntries := (List.range st.lossHistory.length).map (fun i =>
        let l := st.lossHistory.getD i 0
        let fmt := let s := toString l; if s.length > 32 then s.take 32 ++ "…" else s
        s!"gd_iter={i} loss={fmt}")
      let weightNorm := l2NormSq st.currentWeights
      let initNorm := l2NormSq initial
      let wDelta := l2NormSq (sub st.currentWeights initial)
      let fmtR (r : Rat) : String := let s := toString r; if s.length > 32 then s.take 32 ++ "…" else s
      [s!"gd_summary iters={st.iteration} init_norm={fmtR initNorm} final_norm={fmtR weightNorm} weight_delta_norm={fmtR wDelta} final_loss={fmtR st.currentLoss}"] ++ lossEntries
    else
      []
  let symbolicSummaries := symbolicSummariesRaw ++ gdTraceSymbolic
  let preferredCandidates := preferTactic cfg.preferredTactic candidates
  let diversifiedCandidates :=
    if cfg.enableTacticDiversification then
      diversifyTactics preferredCandidates (usageTrackerOf preferredCandidates) (max 1 cfg.diversityTopK)
    else
      preferredCandidates.take (max 1 cfg.decodeTopK)
  let baseProgress :=
    estimateProgress
      initial
      st.currentWeights
      st.iteration
      st.lossHistory
      st.currentLoss
      (max 1 cfg.maxIterations)
  let oracleProgress := clamp01 (verdict.monotonicityScore / 5)
  let progressScore := clamp01 ((baseProgress + oracleProgress) / 2)
  let diversityIdx := tacticDiversityIndex diversifiedCandidates
  {
    lens := lens
    encoded := encoded
    state := st
    verdict := verdict
    psrLoss := psrNow
    dialecticLoss := dialNow
    occamLoss := occamNow
    psrDynamicsLoss := dynNow
    curriculumWeight := currNow
    sheafResolution := resolutionForLens lens
    sheafBasisSize := basisSizeForLens lens
    attentionKeywords := attentionKeywords
    premiseHintsUsed := premiseHints
    gradientProbes := []
    candidates := diversifiedCandidates
    multiwayMode := cfg.useMultiwayGD
    trackMode := cfg.trackMode
    trackConverged := trackConverged
    trackCellCount := trackCellCount
    trackStabilityScore := trackStabilityScore
    symbolicSummaries := symbolicSummaries
    progressScore := progressScore
    tacticDiversityIndex := diversityIdx
    laneDecision := .stay
  }

private def reverseLensHistory (segments : List LaneSegment) : List LensID :=
  (segments.map (fun s => s.lens)).reverse

private def withDecision (seg : LaneSegment) (d : LaneDecision) : LaneSegment :=
  { seg with laneDecision := d }

def run
    (goal : String)
    (cfg : OrchestratorConfig := {})
    (contextHints : List String := [])
    (initialCarry : Option FSum := none) : Result :=
  let startPos : ProofPosition := { lens := cfg.currentLens, depth := 0, history := [] }
  let applyDecision (pos : ProofPosition) (d : LaneDecision) : ProofPosition × LaneDecision :=
    match d with
    | .stay =>
        ({ pos with depth := pos.depth + 1, history := pos.lens :: pos.history }, .stay)
    | .switch lens =>
        ({ lens := lens, depth := pos.depth + 1, history := pos.lens :: pos.history }, .switch lens)
  let rec go
      (remainingChanges : Nat)
      (remainingBudget : Nat)
      (pos : ProofPosition)
      (carry : Option FSum)
      (segmentsRev : List LaneSegment)
      (transportUsed : Bool) : List LaneSegment × Bool :=
    let seg0 := runSingleLane cfg goal pos.lens carry contextHints
    let beliefs := beliefsFrom pos seg0.verdict.stuck
    let gradientDecision :=
      if cfg.useGradientSelection && seg0.verdict.stuck then
        selectLaneByGradient
          goal
          pos.lens
          (some seg0.state.currentWeights)
          cfg.probeConfig
          cfg.regularization
          (probeModeOf cfg.gdMode)
          contextHints
      else
        (.stay, [])
    let fallbackDecision := selectLane beliefs pos
    let decision :=
      if cfg.useGradientSelection && seg0.verdict.stuck then
        gradientDecision.1
      else
        fallbackDecision
    let probes :=
      if cfg.useGradientSelection && seg0.verdict.stuck then
        gradientDecision.2
      else
        []
    let seg := { seg0 with gradientProbes := probes }
    match remainingChanges with
    | 0 =>
        (withDecision seg decision :: segmentsRev, transportUsed)
    | Nat.succ changes =>
      let canSwitch := seg.verdict.stuck && remainingBudget > 0
      if canSwitch then
          match decision with
          | .switch _ =>
              let (nextPos, stepDecision) := applyDecision pos decision
              let carried :=
                match probes.find? (fun p => p.lens = nextPos.lens) with
                | some probe => some probe.finalWeights
                | none =>
                    if cfg.useMultiwayGD then
                      let gdCfg := gdConfigOf cfg (basisForLens pos.lens)
                      let macroCfg := macroConfigOf cfg gdCfg
                      let ms : MacroState :=
                        {
                          currentState := seg.state.currentWeights
                          examples := seg.encoded.examples
                          lockedHistory := []
                          macroStep := 0
                          lossHistory := []
                          converged := false
                          reason := "transport_retry_seed"
                        }
                      let retry := multiwayTransportAndRetry macroCfg ms pos.lens nextPos.lens cfg.useSheafTransport
                      some retry.currentState
                    else if cfg.useSheafTransport then
                      some <| LaxCrossLensTransport.forward sheafTransport pos.lens nextPos.lens seg.state.currentWeights
                    else
                      some <| CrossLensTransport.forward categoricalTransport pos.lens nextPos.lens seg.state.currentWeights
              go changes (remainingBudget - 1) nextPos carried (withDecision seg stepDecision :: segmentsRev) true
          | .stay =>
              (withDecision seg decision :: segmentsRev, transportUsed)
        else
          (withDecision seg decision :: segmentsRev, transportUsed)
  termination_by remainingChanges

  let (segmentsRev, usedTransport) :=
    go cfg.maxLaneChanges cfg.lensBudget startPos initialCarry [] false
  let ordered := segmentsRev.reverse
  let bestSeg :=
    match chooseBestSegment? ordered with
    | some s => s
    | none => runSingleLane cfg goal cfg.currentLens none contextHints
  let reason :=
    if bestSeg.verdict.converged then
      "converged"
    else if bestSeg.verdict.stuck then
      "stuck_after_lane_budget"
    else
      bestSeg.verdict.reason
  let categoricalEvidence : CategoricalEvidence :=
    {
      algebraHomWitness := True
      stepPreservesEvidence := True
      mapFixedUsed := True
      witnessTheorems := categoricalWitnessTheorems
      transportMode := if cfg.useSheafTransport then sheafTransportMode else "algebra_hom_transport"
    }
  {
    ok := supportsGoal goal
    goal := goal
    segments := ordered
    laneHistory := reverseLensHistory segmentsRev
    laneChangesUsed := if ordered.isEmpty then 0 else ordered.length - 1
    finalLens := bestSeg.lens
    bestWeights := bestSeg.state.currentWeights
    bestCandidates := bestSeg.candidates
    psrLoss := bestSeg.psrLoss
    dialecticLoss := bestSeg.dialecticLoss
    occamLoss := bestSeg.occamLoss
    psrDynamicsLoss := bestSeg.psrDynamicsLoss
    psrConverged := bestSeg.verdict.psrConverged
    monotonicityScore := bestSeg.verdict.monotonicityScore
    sheafFinalResolution := bestSeg.sheafResolution
    sheafFinalBasisSize := bestSeg.sheafBasisSize
    attentionKeywords := bestSeg.attentionKeywords
    premiseHintsUsed := bestSeg.premiseHintsUsed
    gdMode := cfg.gdMode
    trackMode := cfg.trackMode
    trackConverged := bestSeg.trackConverged
    trackCellCount := bestSeg.trackCellCount
    trackStabilityScore := bestSeg.trackStabilityScore
    symbolicSummaries := bestSeg.symbolicSummaries
    progressScore := bestSeg.progressScore
    tacticDiversityIndex := bestSeg.tacticDiversityIndex
    categoricalEvidence := categoricalEvidence
    useSheafTransport := cfg.useSheafTransport
    useMultiwayGD := cfg.useMultiwayGD
    reason := reason
    transportUsed := usedTransport
  }

end DifferentiableATP
end ATP
end HeytingLean
