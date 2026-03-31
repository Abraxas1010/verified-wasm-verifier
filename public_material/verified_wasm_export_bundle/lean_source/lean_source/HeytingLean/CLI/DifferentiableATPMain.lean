import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.ATP.DifferentiableATP.FeedbackBridge
import HeytingLean.ATP.DifferentiableATP.OracleEncoder
import HeytingLean.ATP.DifferentiableATP.SearchTree

/-!
# `differentiable_atp`

End-to-end executable for differentiable ATP experimentation:
- goal encoding
- projected gradient descent
- lane-changing orchestration
- kernel verification
- structured feedback payload
-/

namespace HeytingLean
namespace CLI
namespace DifferentiableATPMain

open Lean
open HeytingLean.Embeddings
open HeytingLean.ATP
open HeytingLean.ATP.DifferentiableATP

private def usage : String :=
  String.intercalate "\n"
    [ "differentiable_atp - differentiable proof-search harness"
    , ""
    , "Usage:"
    , "  lake exe differentiable_atp -- --goal \"⊢ True\" [options]"
    , ""
    , "Options:"
    , "  --goal <expr>                Goal expression (required)"
    , "  --current-lens <name>        omega|region|graph|clifford|tensor|topology"
    , "  --target-lens <name>         Optional target lens hint"
    , "  --max-iterations <n>         Gradient steps per lane (default: 24)"
    , "  --max-lane-changes <n>       Max lane switches (default: 2)"
    , "  --lens-budget <n>            Lane-switch budget (default: 3)"
    , "  --max-decoder-candidates <n> Max tactic candidates to verify (default: 4)"
    , "  --multiway-gd                Use step-based multiway GD objective"
    , "  --soft-depth <n>             Structural kernel depth (default: 3)"
    , "  --step-fuel <n>              Step forward-map fuel (default: 1)"
    , "  --simplicity-weight <rat>    Simplicity regularization (default: 1/100)"
    , "  --reach-loss                 Enable reachability-based loss term"
    , "  --no-reach-loss              Disable reachability loss (default)"
    , "  --reach-fuel <n>             Reachability expansion depth (default: 2)"
    , "  --reach-weight <rat>         Reachability loss weight (default: 1/10)"
    , "  --max-macro-steps <n>        Multiway macro-loop budget (default: 5)"
    , "  --inner-iterations <n>       Multiway inner GD iterations (default: 20)"
    , "  --lock-top-k <n>             Terms to keep at each lock step (default: 6)"
    , "  --exact-grad                 Use exact analytic step gradients (default)"
    , "  --finite-diff-grad           Use finite-difference step gradients"
    , "  --learned-tactics            Use learned tactic embedding ranking"
    , "  --static-tactics             Use static combinator→tactic decoding (default)"
    , "  --kan-selector               Use KAN selector as primary tactic ranker"
    , "  --no-kan-selector            Disable KAN selector (default)"
    , "  --oracle-encode              Use oracle probe examples for goal encoding"
    , "  --no-oracle-encode           Disable oracle probe examples (default)"
    , "  --iterative-search           Enable multi-step iterative proof search"
    , "  --no-iterative-search        Disable iterative search (default)"
    , "  --structural-injection       Force structural tactic injection (default)"
    , "  --no-structural-injection    Disable structural tactic injection"
    , "  --search-max-depth <n>       Iterative search max depth (default: 5)"
    , "  --search-max-attempts <n>    Iterative search global attempt budget (default: 200)"
    , "  --search-max-branches <n>    Branches per node (default: 4)"
    , "  --conjunction-branch-budget <n> Branch budget for conjunction goals (default: 6)"
    , "  --search-gd-budget <n>       GD iterations per subgoal (default: 12)"
    , "  --search-macro-steps <n>     Macro steps per subgoal (default: 3)"
    , "  --search-parallel-subgoal-workers <n> Parallel observer workers for subgoal-heavy search (default: 1)"
    , "  --search-subgoal-max-lane-changes <n>  Lane changes allowed per subgoal (default: 0)"
    , "  --search-subgoal-lens-budget <n>       Lens budget per subgoal (default: 1)"
    , "  --search-timeout-seconds <n>    Internal iterative timeout (default: 0 = disabled)"
    , "  --search-observer-timeout-seconds <n> Per-batch observer verification timeout (default: 60)"
    , "  --search-warm-start          Reuse parent GD weights for child subgoals"
    , "  --no-search-warm-start       Disable warm start (default)"
    , "  --track-mode <mode>          baseline|kan|nca|kan_nca (default: baseline)"
    , "  --nca-max-steps <n>          NCA / KAN-NCA max local update steps (default: 12)"
    , "  --nca-tolerance <rat>        NCA stability tolerance (default: 1/1000)"
    , "  --nca-perturb-step <n>       Optional 1-based perturb step (0 disables; default: 0)"
    , "  --nca-perturb-drop <rat>     Optional alive-drop fraction at perturb step (default: 0)"
    , "  --nca-perturb-seed <n>       Perturbation seed (default: 0)"
    , "  --enable-track-training      Enable per-goal track training from provided samples"
    , "  --no-track-training          Disable per-goal track training (default)"
    , "  --track-training-iterations <n>  Training iterations (default: 12)"
    , "  --track-training-learning-rate <rat> Training learning rate (default: 1/100)"
    , "  --track-training-sample-budget <n>  Max training samples per goal (default: 9)"
    , "  --track-training-param-budget <n>   Max trained parameters per step (default: 10)"
    , "  --track-training-loss-steps <n>     NCA training-loss rollout steps (default: 8)"
    , "  --train-sample <goal>::<tactic> Training sample pair (repeatable)"
    , "  --enable-tactic-diversity    Diversify candidate tactics (default)"
    , "  --no-tactic-diversity        Disable diversification"
    , "  --diversity-top-k <n>        Diversity budget (default: 4)"
    , "  --preferred-tactic <name>    Optional tactic preference hint"
    , "  --expand-fallbacks           Generate tactic compositions from GD candidates"
    , "  --no-expand-fallbacks        Disable tactic compositions (default)"
    , "  --emit-gd-trace              Emit per-iteration GD and training diagnostics"
    , "  --context <hint>             Optional context hint (repeatable)"
    , "  --json                       Print machine-readable JSON"
    , "  --help                       Show this message"
    ]

structure Config where
  goal : Option String := none
  currentLens : LensID := .omega
  targetLens : Option LensID := none
  maxIterations : Nat := 24
  maxLaneChanges : Nat := 2
  lensBudget : Nat := 3
  maxDecoderCandidates : Nat := 4
  useMultiwayGD : Bool := false
  softDepth : Nat := 3
  stepFuel : Nat := 1
  simplicityWeight : Rat := (1 : Rat) / 100
  useReachLoss : Bool := false
  reachFuel : Nat := 2
  reachWeight : Rat := (1 : Rat) / 10
  maxMacroSteps : Nat := 5
  innerIterations : Nat := 20
  lockTopK : Nat := 6
  exactGrad : Bool := true
  learnedTactics : Bool := false
  kanSelector : Bool := false
  oracleEncode : Bool := false
  iterativeSearch : Bool := false
  structuralInjection : Bool := true
  searchMaxDepth : Nat := 5
  searchMaxAttempts : Nat := 200
  searchMaxBranches : Nat := 4
  conjunctionBranchBudget : Nat := 6
  searchGDBudget : Nat := 12
  searchMacroSteps : Nat := 3
  searchParallelSubgoalWorkers : Nat := 1
  searchSubgoalMaxLaneChanges : Nat := 0
  searchSubgoalLensBudget : Nat := 1
  searchTimeoutSeconds : Nat := 0
  searchObserverTimeoutSeconds : Nat := 60
  searchWarmStart : Bool := false
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
  enableTacticDiversification : Bool := true
  diversityTopK : Nat := 4
  preferredTactic : Option String := none
  expandFallbacks : Bool := false
  emitGDTrace : Bool := false
  contextHints : List String := []
  jsonOutput : Bool := false
  deriving Repr

private def parseLens? (s : String) : Option LensID :=
  match s.trim.toLower with
  | "omega" => some .omega
  | "region" => some .region
  | "graph" => some .graph
  | "clifford" => some .clifford
  | "tensor" => some .tensor
  | "topology" => some .topology
  | "matula" => some .matula
  | _ => none

private def parseRat? (s : String) : Option Rat :=
  let t := s.trim
  if t.isEmpty then
    none
  else
    match t.splitOn "/" with
    | [nStr, dStr] =>
        match nStr.trim.toInt?, dStr.trim.toInt? with
        | some n, some d =>
            if d = 0 then none else some ((n : Rat) / (d : Rat))
        | _, _ => none
    | _ =>
        match t.toInt? with
        | some n => some (n : Rat)
        | none => none

private def parseTrackMode? (s : String) : Option TrackMode :=
  match s.trim.toLower with
  | "baseline" => some .baseline
  | "kan" => some .kan
  | "nca" => some .nca
  | "kan_nca" => some .kan_nca
  | _ => none

private def parseTrainSample? (s : String) : Option (String × String) :=
  let parts := s.splitOn "::"
  match parts with
  | [] => none
  | [_] => none
  | goal :: tacticParts =>
      let g := goal.trim
      let t := String.intercalate "::" tacticParts |>.trim
      if g.isEmpty || t.isEmpty then none else some (g, t)

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) := do
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--json" :: rest => parseArgs rest { cfg with jsonOutput := true }
  | "--goal" :: goal :: rest => parseArgs rest { cfg with goal := some goal }
  | "--current-lens" :: lens :: rest =>
      match parseLens? lens with
      | some l => parseArgs rest { cfg with currentLens := l }
      | none => throw <| IO.userError s!"invalid lens: {lens}"
  | "--target-lens" :: lens :: rest =>
      match parseLens? lens with
      | some l => parseArgs rest { cfg with targetLens := some l }
      | none => throw <| IO.userError s!"invalid lens: {lens}"
  | "--max-iterations" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with maxIterations := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --max-iterations: {n}"
  | "--max-lane-changes" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with maxLaneChanges := v }
      | none => throw <| IO.userError s!"invalid nat for --max-lane-changes: {n}"
  | "--lens-budget" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with lensBudget := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --lens-budget: {n}"
  | "--max-decoder-candidates" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with maxDecoderCandidates := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --max-decoder-candidates: {n}"
  | "--multiway-gd" :: rest => parseArgs rest { cfg with useMultiwayGD := true }
  | "--soft-depth" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with softDepth := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --soft-depth: {n}"
  | "--step-fuel" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with stepFuel := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --step-fuel: {n}"
  | "--simplicity-weight" :: w :: rest =>
      match parseRat? w with
      | some v => parseArgs rest { cfg with simplicityWeight := v }
      | none => throw <| IO.userError s!"invalid rational for --simplicity-weight: {w}"
  | "--reach-loss" :: rest => parseArgs rest { cfg with useReachLoss := true }
  | "--no-reach-loss" :: rest => parseArgs rest { cfg with useReachLoss := false }
  | "--reach-fuel" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with reachFuel := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --reach-fuel: {n}"
  | "--reach-weight" :: w :: rest =>
      match parseRat? w with
      | some v => parseArgs rest { cfg with reachWeight := v }
      | none => throw <| IO.userError s!"invalid rational for --reach-weight: {w}"
  | "--max-macro-steps" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with maxMacroSteps := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --max-macro-steps: {n}"
  | "--inner-iterations" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with innerIterations := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --inner-iterations: {n}"
  | "--lock-top-k" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with lockTopK := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --lock-top-k: {n}"
  | "--exact-grad" :: rest => parseArgs rest { cfg with exactGrad := true }
  | "--finite-diff-grad" :: rest => parseArgs rest { cfg with exactGrad := false }
  | "--learned-tactics" :: rest => parseArgs rest { cfg with learnedTactics := true }
  | "--static-tactics" :: rest => parseArgs rest { cfg with learnedTactics := false }
  | "--kan-selector" :: rest => parseArgs rest { cfg with kanSelector := true }
  | "--no-kan-selector" :: rest => parseArgs rest { cfg with kanSelector := false }
  | "--oracle-encode" :: rest => parseArgs rest { cfg with oracleEncode := true }
  | "--no-oracle-encode" :: rest => parseArgs rest { cfg with oracleEncode := false }
  | "--iterative-search" :: rest => parseArgs rest { cfg with iterativeSearch := true }
  | "--no-iterative-search" :: rest => parseArgs rest { cfg with iterativeSearch := false }
  | "--structural-injection" :: rest => parseArgs rest { cfg with structuralInjection := true }
  | "--no-structural-injection" :: rest => parseArgs rest { cfg with structuralInjection := false }
  | "--search-max-depth" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchMaxDepth := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --search-max-depth: {n}"
  | "--search-max-attempts" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchMaxAttempts := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --search-max-attempts: {n}"
  | "--search-max-branches" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchMaxBranches := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --search-max-branches: {n}"
  | "--conjunction-branch-budget" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with conjunctionBranchBudget := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --conjunction-branch-budget: {n}"
  | "--search-gd-budget" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchGDBudget := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --search-gd-budget: {n}"
  | "--search-macro-steps" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchMacroSteps := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --search-macro-steps: {n}"
  | "--search-parallel-subgoal-workers" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchParallelSubgoalWorkers := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --search-parallel-subgoal-workers: {n}"
  | "--search-subgoal-max-lane-changes" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchSubgoalMaxLaneChanges := v }
      | none => throw <| IO.userError s!"invalid nat for --search-subgoal-max-lane-changes: {n}"
  | "--search-subgoal-lens-budget" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchSubgoalLensBudget := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --search-subgoal-lens-budget: {n}"
  | "--search-timeout-seconds" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchTimeoutSeconds := v }
      | none => throw <| IO.userError s!"invalid nat for --search-timeout-seconds: {n}"
  | "--search-observer-timeout-seconds" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchObserverTimeoutSeconds := max 10 v }
      | none => throw <| IO.userError s!"invalid nat for --search-observer-timeout-seconds: {n}"
  | "--search-warm-start" :: rest => parseArgs rest { cfg with searchWarmStart := true }
  | "--no-search-warm-start" :: rest => parseArgs rest { cfg with searchWarmStart := false }
  | "--track-mode" :: mode :: rest =>
      match parseTrackMode? mode with
      | some m => parseArgs rest { cfg with trackMode := m }
      | none => throw <| IO.userError s!"invalid track mode: {mode}"
  | "--nca-max-steps" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with ncaMaxSteps := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --nca-max-steps: {n}"
  | "--nca-tolerance" :: t :: rest =>
      match parseRat? t with
      | some v => parseArgs rest { cfg with ncaTolerance := v }
      | none => throw <| IO.userError s!"invalid rational for --nca-tolerance: {t}"
  | "--nca-perturb-step" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with ncaPerturbStep := v }
      | none => throw <| IO.userError s!"invalid nat for --nca-perturb-step: {n}"
  | "--nca-perturb-drop" :: t :: rest =>
      match parseRat? t with
      | some v => parseArgs rest { cfg with ncaPerturbDrop := v }
      | none => throw <| IO.userError s!"invalid rational for --nca-perturb-drop: {t}"
  | "--nca-perturb-seed" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with ncaPerturbSeed := v }
      | none => throw <| IO.userError s!"invalid nat for --nca-perturb-seed: {n}"
  | "--enable-track-training" :: rest => parseArgs rest { cfg with enableTrackTraining := true }
  | "--no-track-training" :: rest => parseArgs rest { cfg with enableTrackTraining := false }
  | "--track-training-iterations" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with trackTrainingIterations := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --track-training-iterations: {n}"
  | "--track-training-learning-rate" :: w :: rest =>
      match parseRat? w with
      | some v => parseArgs rest { cfg with trackTrainingLearningRate := v }
      | none => throw <| IO.userError s!"invalid rational for --track-training-learning-rate: {w}"
  | "--track-training-sample-budget" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with trackTrainingSampleBudget := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --track-training-sample-budget: {n}"
  | "--track-training-param-budget" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with trackTrainingParamBudget := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --track-training-param-budget: {n}"
  | "--track-training-loss-steps" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with trackTrainingLossSteps := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --track-training-loss-steps: {n}"
  | "--train-sample" :: sample :: rest =>
      match parseTrainSample? sample with
      | some pair => parseArgs rest { cfg with trainingSamples := cfg.trainingSamples ++ [pair] }
      | none => throw <| IO.userError s!"invalid --train-sample format (expected <goal>::<tactic>): {sample}"
  | "--enable-tactic-diversity" :: rest => parseArgs rest { cfg with enableTacticDiversification := true }
  | "--no-tactic-diversity" :: rest => parseArgs rest { cfg with enableTacticDiversification := false }
  | "--diversity-top-k" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with diversityTopK := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --diversity-top-k: {n}"
  | "--preferred-tactic" :: t :: rest => parseArgs rest { cfg with preferredTactic := some t }
  | "--expand-fallbacks" :: rest => parseArgs rest { cfg with expandFallbacks := true }
  | "--no-expand-fallbacks" :: rest => parseArgs rest { cfg with expandFallbacks := false }
  | "--emit-gd-trace" :: rest => parseArgs rest { cfg with emitGDTrace := true }
  | "--context" :: h :: rest => parseArgs rest { cfg with contextHints := cfg.contextHints ++ [h] }
  | x :: _ => throw <| IO.userError s!"unknown argument: {x}"

private def lensName : LensID → String
  | .omega => "omega"
  | .region => "region"
  | .graph => "graph"
  | .clifford => "clifford"
  | .tensor => "tensor"
  | .topology => "topology"
  | .matula => "matula"

private def trackModeName : TrackMode → String
  | .baseline => "baseline"
  | .kan => "kan"
  | .nca => "nca"
  | .kan_nca => "kan_nca"

private def traceRow (cfg : Config) (run : Result) (payload : FeedbackPayload) : Json :=
  let candidates :=
    Json.arr <| run.bestCandidates.toArray.map (fun c =>
      Json.mkObj [ ("kind", Json.str "decoded_tactic"), ("id", Json.str c.tactic) ])
  Json.mkObj
    [ ("schema", Json.str "atp_sheaf_glue_trace_row_v1")
    , ("source", Json.str "differentiable_atp")
    , ("run_id", Json.str s!"differentiable_atp_{hash run.goal}")
    , ("goal", Json.str run.goal)
    , ("context_features", Json.mkObj
        [ ("current_lens", Json.str (lensName cfg.currentLens))
        , ("target_lens", match cfg.targetLens with | some l => Json.str (lensName l) | none => Json.null)
        , ("max_iterations", Json.num cfg.maxIterations)
        , ("max_lane_changes", Json.num cfg.maxLaneChanges)
        , ("multiway_gd", Json.bool cfg.useMultiwayGD)
        , ("soft_depth", Json.num cfg.softDepth)
        , ("step_fuel", Json.num cfg.stepFuel)
        , ("simplicity_weight", Json.str (toString cfg.simplicityWeight))
        , ("max_macro_steps", Json.num cfg.maxMacroSteps)
        , ("inner_iterations", Json.num cfg.innerIterations)
        , ("lock_top_k", Json.num cfg.lockTopK)
        , ("exact_grad", Json.bool cfg.exactGrad)
        , ("learned_tactics", Json.bool cfg.learnedTactics)
        , ("kan_selector", Json.bool cfg.kanSelector)
        , ("oracle_encode", Json.bool cfg.oracleEncode)
        , ("iterative_search", Json.bool cfg.iterativeSearch)
        , ("structural_injection", Json.bool cfg.structuralInjection)
        , ("search_max_depth", Json.num cfg.searchMaxDepth)
        , ("search_max_attempts", Json.num cfg.searchMaxAttempts)
        , ("search_max_branches", Json.num cfg.searchMaxBranches)
        , ("conjunction_branch_budget", Json.num cfg.conjunctionBranchBudget)
        , ("search_gd_budget", Json.num cfg.searchGDBudget)
        , ("search_macro_steps", Json.num cfg.searchMacroSteps)
        , ("search_parallel_subgoal_workers", Json.num cfg.searchParallelSubgoalWorkers)
        , ("search_subgoal_max_lane_changes", Json.num cfg.searchSubgoalMaxLaneChanges)
        , ("search_subgoal_lens_budget", Json.num cfg.searchSubgoalLensBudget)
        , ("search_timeout_seconds", Json.num cfg.searchTimeoutSeconds)
        , ("search_observer_timeout_seconds", Json.num cfg.searchObserverTimeoutSeconds)
        , ("search_warm_start", Json.bool cfg.searchWarmStart)
        , ("track_mode", Json.str (trackModeName cfg.trackMode))
        , ("nca_max_steps", Json.num cfg.ncaMaxSteps)
        , ("nca_tolerance", Json.str (toString cfg.ncaTolerance))
        , ("nca_perturb_step", Json.num cfg.ncaPerturbStep)
        , ("nca_perturb_drop", Json.str (toString cfg.ncaPerturbDrop))
        , ("nca_perturb_seed", Json.num cfg.ncaPerturbSeed)
        , ("enable_track_training", Json.bool cfg.enableTrackTraining)
        , ("track_training_iterations", Json.num cfg.trackTrainingIterations)
        , ("track_training_learning_rate", Json.str (toString cfg.trackTrainingLearningRate))
        , ("track_training_sample_budget", Json.num cfg.trackTrainingSampleBudget)
        , ("track_training_param_budget", Json.num cfg.trackTrainingParamBudget)
        , ("track_training_loss_steps", Json.num cfg.trackTrainingLossSteps)
        , ("training_samples_count", Json.num cfg.trainingSamples.length)
        , ("enable_tactic_diversification", Json.bool cfg.enableTacticDiversification)
        , ("diversity_top_k", Json.num cfg.diversityTopK)
        , ("preferred_tactic", match cfg.preferredTactic with | some t => Json.str t | none => Json.null)
        ])
    , ("candidate_set", candidates)
    , ("chosen_action", Json.mkObj
        [ ("lane_changes_used", Json.num run.laneChangesUsed)
        , ("final_lens", Json.str (lensName run.finalLens))
        , ("selected_tactic", match payload.selectedTactic with | some t => Json.str t | none => Json.null)
        ])
    , ("outcome", Json.mkObj
        [ ("status_after", Json.str (if payload.proved then "proved" else "blocked"))
        , ("reason", Json.str payload.reason)
        ])
    , ("cost_metrics", Json.mkObj [ ("segments", Json.num run.segments.length) ])
    , ("lane_metadata", Json.mkObj
        [ ("primary_lane", Json.str "differentiable")
        , ("lane_history", Json.arr <| run.laneHistory.toArray.map (fun l => Json.str (lensName l)))
        ])
    , ("transport_metadata", Json.mkObj [ ("transport_used", Json.bool run.transportUsed) ])
    ]

private def iterativeSelectedTactic? (steps : List (String × String)) : Option String :=
  match steps.reverse with
  | [] => none
  | (_, tactic) :: _ => some tactic

private def iterativeScriptText? (steps : List (String × String)) : Option String :=
  if steps.isEmpty then
    none
  else
    some <| String.intercalate "; " (steps.map Prod.snd)

private def searchResultToJson (res : SearchResult) : Json :=
  let script :=
    Json.arr <| res.proofScript.toArray.map (fun row =>
      Json.mkObj [("goal", Json.str row.1), ("tactic", Json.str row.2)])
  let tree :=
    Json.arr <| res.searchTree.toArray.map (fun n =>
      Json.mkObj
        [ ("goal", Json.str n.goal)
        , ("depth", Json.num n.depth)
        , ("priority", Json.str (toString n.priorityScore))
        , ("parent_tactic", match n.parentTactic with | some t => Json.str t | none => Json.null)
        , ("preferred_tactic", match n.preferredTactic with | some t => Json.str t | none => Json.null)
        ])
  let rejections :=
    Json.arr <| res.candidateRejections.toArray.map (fun r =>
      Json.mkObj
        [ ("node_goal", Json.str r.nodeGoal)
        , ("node_depth", Json.num r.nodeDepth)
        , ("tactic", Json.str r.tactic)
        , ("reason", Json.str r.reason)
        , ("remaining_goals", Json.arr <| r.remainingGoals.toArray.map Json.str)
        , ("observer_stderr_excerpt", Json.str r.observerStderrExcerpt)
        ])
  let training :=
    Json.arr <| res.trainingSamples.toArray.map (fun row =>
      Json.mkObj [("goal", Json.str row.1), ("tactic", Json.str row.2)])
  let enriched :=
    Json.arr <| res.enrichedTrainingSamples.toArray.map (fun row =>
      Json.mkObj
        [ ("goal", Json.str row.goal)
        , ("expected_tactic", Json.str row.expectedTactic)
        , ("subgoals_solved", Json.num row.subgoalsSolved)
        , ("total_subgoals", Json.num row.totalSubgoals)
        , ("composition_bonus", Json.str (toString row.compositionBonus))
        ])
  Json.mkObj
    [ ("proved", Json.bool res.proved)
    , ("reason", Json.str res.reason)
    , ("nodes_explored", Json.num res.nodesExplored)
    , ("max_depth_reached", Json.num res.maxDepthReached)
    , ("total_attempts", Json.num res.totalAttempts)
    , ("backtrack_count", Json.num res.backtrackCount)
    , ("proof_script", script)
    , ("search_tree", tree)
    , ("candidate_rejections", rejections)
    , ("training_samples", training)
    , ("enriched_training_samples", enriched)
    ]

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  if args.isEmpty then
    IO.println usage
    return (0 : UInt32)
  try
    let (cfg, showHelp) ← parseArgs args
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let some goal := cfg.goal
      | do
        IO.eprintln "Error: --goal is required"
        IO.eprintln usage
        return (3 : UInt32)

    let oracleExamples? : Option (List HeytingLean.LoF.Combinators.Differential.Compute.IOExample) ←
      if cfg.oracleEncode then
        try
          let rows ← oracleEncode goal
          if rows.isEmpty then pure none else pure (some rows)
        catch _ =>
          pure none
      else
        pure none

    let runCfg : OrchestratorConfig :=
      {
        currentLens := cfg.currentLens
        maxIterations := cfg.maxIterations
        maxLaneChanges := cfg.maxLaneChanges
        lensBudget := cfg.lensBudget
        decodeTopK := cfg.maxDecoderCandidates
        useMultiwayGD := cfg.useMultiwayGD
        softKernelDepth := cfg.softDepth
        stepFuel := cfg.stepFuel
        simplicityWeight := cfg.simplicityWeight
        useReachLoss := cfg.useReachLoss
        reachFuel := cfg.reachFuel
        reachWeight := cfg.reachWeight
        maxMacroSteps := cfg.maxMacroSteps
        innerIterations := cfg.innerIterations
        lockTopK := cfg.lockTopK
        exactGradient := cfg.exactGrad
        useLearnedTactics := cfg.learnedTactics
        useKANSelector := cfg.kanSelector
        useOracleEncoding := cfg.oracleEncode
        oracleExamples := oracleExamples?
        useStructuralInjection := cfg.structuralInjection
        trackMode := cfg.trackMode
        ncaMaxSteps := cfg.ncaMaxSteps
        ncaTolerance := cfg.ncaTolerance
        ncaPerturbStep := cfg.ncaPerturbStep
        ncaPerturbDrop := cfg.ncaPerturbDrop
        ncaPerturbSeed := cfg.ncaPerturbSeed
        enableTrackTraining := cfg.enableTrackTraining
        trackTrainingIterations := cfg.trackTrainingIterations
        trackTrainingLearningRate := cfg.trackTrainingLearningRate
        trackTrainingSampleBudget := cfg.trackTrainingSampleBudget
        trackTrainingParamBudget := cfg.trackTrainingParamBudget
        trackTrainingLossSteps := cfg.trackTrainingLossSteps
        trainingSamples := cfg.trainingSamples
        enrichedTrainingSamples := []
        enableTacticDiversification := cfg.enableTacticDiversification
        diversityTopK := cfg.diversityTopK
        preferredTactic := cfg.preferredTactic
        emitGDTrace := cfg.emitGDTrace
      }
    let searchCfg : SearchConfig :=
      {
        maxDepth := max 1 cfg.searchMaxDepth
        maxTotalAttempts := max 1 cfg.searchMaxAttempts
        maxBranches := max 1 cfg.searchMaxBranches
        conjunctionBranchBudget := max 1 cfg.conjunctionBranchBudget
        gdBudget := max 1 cfg.searchGDBudget
        macroSteps := max 1 cfg.searchMacroSteps
        parallelSubgoalWorkers := max 1 cfg.searchParallelSubgoalWorkers
        subgoalMaxLaneChanges := cfg.searchSubgoalMaxLaneChanges
        subgoalLensBudget := max 1 cfg.searchSubgoalLensBudget
        searchTimeoutSeconds := cfg.searchTimeoutSeconds
        observerTimeoutSeconds := cfg.searchObserverTimeoutSeconds
        warmStart := cfg.searchWarmStart
      }

    -- When expand-fallbacks is active, decode more candidates from GD so they get
    -- sourced as "learned::" instead of "fallback". Also increase diversity budget
    -- to keep all decoded candidates through the diversification pipeline.
    let expandedRunCfg :=
      if cfg.expandFallbacks then
        { runCfg with
          decodeTopK := max 12 runCfg.decodeTopK
          diversityTopK := max 12 cfg.diversityTopK }
      else
        runCfg
    let runResult := HeytingLean.ATP.DifferentiableATP.run goal expandedRunCfg cfg.contextHints
    let searchKANSelector? : Option HeytingLean.ATP.DifferentiableATP.KANTacticSelector :=
      if cfg.kanSelector then
        if cfg.enableTrackTraining && !cfg.trainingSamples.isEmpty then
          let (trained, _, _) :=
            HeytingLean.ATP.DifferentiableATP.trainKANOnGoals
              cfg.trainingSamples
              HeytingLean.ATP.DifferentiableATP.warmStartSelector
              (max 1 cfg.trackTrainingIterations)
              cfg.trackTrainingLearningRate
              ((1 : Rat) / 1000)
              (max 1 cfg.trackTrainingSampleBudget)
              (max 1 cfg.trackTrainingParamBudget)
          some trained
        else
          some HeytingLean.ATP.DifferentiableATP.warmStartSelector
      else
        none
    let iterativeResult0? : Option SearchResult ←
      if cfg.iterativeSearch then
        some <$> HeytingLean.ATP.DifferentiableATP.search goal searchCfg expandedRunCfg cfg.contextHints searchKANSelector?
      else
        pure none
    let iterativePair : Option SearchResult × Bool ←
      match iterativeResult0? with
      | some res =>
          let shouldRetrain :=
            cfg.iterativeSearch &&
            cfg.kanSelector &&
            cfg.enableTrackTraining &&
            !res.proved &&
            (!res.trainingSamples.isEmpty || !res.enrichedTrainingSamples.isEmpty)
          if shouldRetrain then
            let mergedLegacy := (cfg.trainingSamples ++ res.trainingSamples).eraseDups
            let baseSelector := searchKANSelector?.getD HeytingLean.ATP.DifferentiableATP.warmStartSelector
            let (retrained, _, _) :=
              HeytingLean.ATP.DifferentiableATP.trainKANOnGoals
                mergedLegacy
                baseSelector
                (max 1 cfg.trackTrainingIterations)
                cfg.trackTrainingLearningRate
                ((1 : Rat) / 1000)
                (max 1 cfg.trackTrainingSampleBudget)
                (max 1 cfg.trackTrainingParamBudget)
                (enrichedSamples := res.enrichedTrainingSamples)
            let rerun ← HeytingLean.ATP.DifferentiableATP.search goal searchCfg expandedRunCfg cfg.contextHints (some retrained)
            pure (some rerun, true)
          else
            pure (some res, false)
      | none =>
          pure (none, false)
    let iterativeResult? := iterativePair.1
    let iterativeRetrainTriggered := iterativePair.2
    -- When multiway GD or expand-fallbacks is active, try more candidates
    let verifyBudget :=
      if cfg.expandFallbacks then max cfg.maxDecoderCandidates 24
      else if cfg.useMultiwayGD then max cfg.maxDecoderCandidates 12
      else cfg.maxDecoderCandidates
    let verifier ←
      match iterativeResult? with
      | some res =>
          if res.proved then
            pure
              {
                ok := true
                verifiedTactic := iterativeScriptText? res.proofScript <|> iterativeSelectedTactic? res.proofScript
                attempts := []
                reason := "iterative_search_proved"
              }
          else
            verify goal runResult.bestCandidates verifyBudget cfg.expandFallbacks
      | none =>
          verify goal runResult.bestCandidates verifyBudget cfg.expandFallbacks
    let payload := buildPayload goal runResult verifier
    let trace := traceRow cfg runResult payload

    let result :=
      Json.mkObj
        [ ("ok", Json.bool payload.ok)
        , ("proved", Json.bool payload.proved)
        , ("reason", Json.str payload.reason)
        , ("goal", Json.str goal)
        , ("current_lens", Json.str (lensName cfg.currentLens))
        , ("target_lens", match cfg.targetLens with | some l => Json.str (lensName l) | none => Json.null)
        , ("final_lens", Json.str (lensName runResult.finalLens))
        , ("lane_changes_used", Json.num runResult.laneChangesUsed)
        , ("transport_used", Json.bool runResult.transportUsed)
        , ("multiway_gd", Json.bool cfg.useMultiwayGD)
        , ("expand_fallbacks", Json.bool cfg.expandFallbacks)
        , ("soft_depth", Json.num cfg.softDepth)
        , ("step_fuel", Json.num cfg.stepFuel)
        , ("simplicity_weight", Json.str (toString cfg.simplicityWeight))
        , ("max_macro_steps", Json.num cfg.maxMacroSteps)
        , ("inner_iterations", Json.num cfg.innerIterations)
        , ("lock_top_k", Json.num cfg.lockTopK)
        , ("exact_grad", Json.bool cfg.exactGrad)
        , ("learned_tactics", Json.bool cfg.learnedTactics)
        , ("kan_selector", Json.bool cfg.kanSelector)
        , ("iterative_search", Json.bool cfg.iterativeSearch)
        , ("iterative_retrain_triggered", Json.bool iterativeRetrainTriggered)
        , ("iterative_first_pass_proved", match iterativeResult0? with | some res => Json.bool res.proved | none => Json.null)
        , ("iterative_first_pass_reason", match iterativeResult0? with | some res => Json.str res.reason | none => Json.null)
        , ("iterative_first_pass_training_samples_count", match iterativeResult0? with | some res => Json.num res.trainingSamples.length | none => Json.null)
        , ("iterative_first_pass_enriched_samples_count", match iterativeResult0? with | some res => Json.num res.enrichedTrainingSamples.length | none => Json.null)
        , ("structural_injection", Json.bool cfg.structuralInjection)
        , ("search_max_depth", Json.num cfg.searchMaxDepth)
        , ("search_max_attempts", Json.num cfg.searchMaxAttempts)
        , ("search_max_branches", Json.num cfg.searchMaxBranches)
        , ("conjunction_branch_budget", Json.num cfg.conjunctionBranchBudget)
        , ("search_gd_budget", Json.num cfg.searchGDBudget)
        , ("search_macro_steps", Json.num cfg.searchMacroSteps)
        , ("search_parallel_subgoal_workers", Json.num cfg.searchParallelSubgoalWorkers)
        , ("search_subgoal_max_lane_changes", Json.num cfg.searchSubgoalMaxLaneChanges)
        , ("search_subgoal_lens_budget", Json.num cfg.searchSubgoalLensBudget)
        , ("search_timeout_seconds", Json.num cfg.searchTimeoutSeconds)
        , ("search_observer_timeout_seconds", Json.num cfg.searchObserverTimeoutSeconds)
        , ("search_warm_start", Json.bool cfg.searchWarmStart)
        , ("track_mode", Json.str (trackModeName cfg.trackMode))
        , ("track_converged", Json.bool runResult.trackConverged)
        , ("track_cell_count", Json.num runResult.trackCellCount)
        , ("track_stability_score", Json.str (toString runResult.trackStabilityScore))
        , ("track_symbolic_summaries", Json.arr <| runResult.symbolicSummaries.toArray.map Json.str)
        , ("progress_score", Json.str (toString runResult.progressScore))
        , ("tactic_diversity_index", Json.str (toString runResult.tacticDiversityIndex))
        , ("nca_perturb_step", Json.num cfg.ncaPerturbStep)
        , ("nca_perturb_drop", Json.str (toString cfg.ncaPerturbDrop))
        , ("nca_perturb_seed", Json.num cfg.ncaPerturbSeed)
        , ("enable_track_training", Json.bool cfg.enableTrackTraining)
        , ("track_training_iterations", Json.num cfg.trackTrainingIterations)
        , ("track_training_learning_rate", Json.str (toString cfg.trackTrainingLearningRate))
        , ("track_training_sample_budget", Json.num cfg.trackTrainingSampleBudget)
        , ("track_training_param_budget", Json.num cfg.trackTrainingParamBudget)
        , ("track_training_loss_steps", Json.num cfg.trackTrainingLossSteps)
        , ("training_samples_count", Json.num cfg.trainingSamples.length)
        , ("enable_tactic_diversification", Json.bool cfg.enableTacticDiversification)
        , ("diversity_top_k", Json.num cfg.diversityTopK)
        , ("preferred_tactic", match cfg.preferredTactic with | some t => Json.str t | none => Json.null)
        , ("selected_tactic", match payload.selectedTactic with | some t => Json.str t | none => Json.null)
        , ("candidate_tactics", Json.arr <| runResult.bestCandidates.toArray.map (fun c => Json.str c.tactic))
        , ("iterative_first_pass_result", match iterativeResult0? with | some res => searchResultToJson res | none => Json.null)
        , ("iterative_search_result", match iterativeResult? with | some res => searchResultToJson res | none => Json.null)
        , ("trace_row", trace)
        , ("feedback", payloadToJson payload)
        ]

    if cfg.jsonOutput then
      IO.println result.compress
    else
      IO.println s!"differentiable_atp: proved={payload.proved} reason={payload.reason}"

    pure (if payload.proved then (0 : UInt32) else (1 : UInt32))

  catch e =>
    IO.eprintln s!"Error: {e}"
    pure (2 : UInt32)

end DifferentiableATPMain
end CLI
end HeytingLean

open HeytingLean.CLI.DifferentiableATPMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.DifferentiableATPMain.main args
