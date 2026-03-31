import Lean.Data.Json
import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.ATP.DifferentiableATP.SearchTree
import HeytingLean.ATP.LensTransport.TransportedSearch

/-!
# `lens_transport_bench`

Small benchmark-facing executable that runs either:
- standard single-lens search, or
- lens-transported search.
-/

namespace HeytingLean
namespace CLI
namespace LensTransportBenchMain

open Lean
open HeytingLean.Embeddings
open HeytingLean.ATP
open HeytingLean.ATP.DifferentiableATP
open HeytingLean.ATP.LensTransport

inductive Mode where
  | standard
  | lensTransport
  deriving Repr, DecidableEq

structure Config where
  goal : Option String := none
  mode : Mode := .standard
  currentLens : LensID := .omega
  maxDepth : Nat := 50
  maxNodes : Nat := 5000
  maxBranches : Nat := 4
  conjunctionBranchBudget : Nat := 6
  observerTimeout : Nat := 15
  gdBudget : Nat := 12
  macroSteps : Nat := 3
  searchTimeout : Nat := 0
  expandFallbacks : Bool := true
  nodesBeforeTransition : Nat := 100
  jsonOutput : Bool := false
  deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "lens_transport_bench - standard vs lens-transported search runner"
    , ""
    , "Usage:"
    , "  lake exe lens_transport_bench -- --goal \"⊢ True\" [options]"
    , ""
    , "Options:"
    , "  --goal <expr>                  Goal expression (required)"
    , "  --mode <name>                  standard|lens_transport (default: standard)"
    , "  --current-lens <name>          omega|region|graph|clifford|tensor|topology|matula"
    , "  --max-depth <n>                Search depth per lens (default: 50)"
    , "  --max-nodes <n>                Node budget (default: 5000)"
    , "  --max-branches <n>             Candidate branches per node (default: 4)"
    , "  --conjunction-branch-budget <n> Branch budget for conjunction goals (default: 6)"
    , "  --observer-timeout <n>         Observer timeout seconds (default: 15)"
    , "  --gd-budget <n>                GD iterations per search node (default: 12)"
    , "  --macro-steps <n>              Macro steps per search node (default: 3)"
    , "  --search-timeout <n>           Internal search timeout seconds (default: 0)"
    , "  --expand-fallbacks             Enable fallback expansion (default)"
    , "  --no-expand-fallbacks          Disable fallback expansion"
    , "  --nodes-before-transition <n>  Budget before transitions (default: 100)"
    , "  --json                         Emit JSON"
    , "  --help                         Show this message"
    ]

private def lensName : LensID → String
  | .omega => "omega"
  | .region => "region"
  | .graph => "graph"
  | .clifford => "clifford"
  | .tensor => "tensor"
  | .topology => "topology"
  | .matula => "matula"

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

private def modeName : Mode → String
  | .standard => "standard"
  | .lensTransport => "lens_transport"

private def parseMode? (s : String) : Option Mode :=
  match s.trim.toLower with
  | "standard" => some .standard
  | "lens_transport" => some .lensTransport
  | _ => none

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) := do
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--json" :: rest => parseArgs rest { cfg with jsonOutput := true }
  | "--goal" :: goal :: rest => parseArgs rest { cfg with goal := some goal }
  | "--mode" :: m :: rest =>
      match parseMode? m with
      | some mode => parseArgs rest { cfg with mode := mode }
      | none => throw <| IO.userError s!"invalid mode: {m}"
  | "--current-lens" :: lens :: rest =>
      match parseLens? lens with
      | some l => parseArgs rest { cfg with currentLens := l }
      | none => throw <| IO.userError s!"invalid lens: {lens}"
  | "--max-depth" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with maxDepth := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --max-depth: {n}"
  | "--max-nodes" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with maxNodes := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --max-nodes: {n}"
  | "--max-branches" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with maxBranches := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --max-branches: {n}"
  | "--conjunction-branch-budget" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with conjunctionBranchBudget := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --conjunction-branch-budget: {n}"
  | "--observer-timeout" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with observerTimeout := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --observer-timeout: {n}"
  | "--gd-budget" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with gdBudget := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --gd-budget: {n}"
  | "--macro-steps" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with macroSteps := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --macro-steps: {n}"
  | "--search-timeout" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with searchTimeout := v }
      | none => throw <| IO.userError s!"invalid nat for --search-timeout: {n}"
  | "--expand-fallbacks" :: rest =>
      parseArgs rest { cfg with expandFallbacks := true }
  | "--no-expand-fallbacks" :: rest =>
      parseArgs rest { cfg with expandFallbacks := false }
  | "--nodes-before-transition" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with nodesBeforeTransition := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --nodes-before-transition: {n}"
  | unknown :: _ =>
      throw <| IO.userError s!"unknown argument: {unknown}"

private def mkSearchConfig (cfg : Config) : SearchConfig :=
  { maxDepth := max 1 cfg.maxDepth
    maxTotalAttempts := max 1 cfg.maxNodes
    maxBranches := max 1 cfg.maxBranches
    conjunctionBranchBudget := max 1 cfg.conjunctionBranchBudget
    gdBudget := max 1 cfg.gdBudget
    macroSteps := max 1 cfg.macroSteps
    searchTimeoutSeconds := cfg.searchTimeout
    observerTimeoutSeconds := max 1 cfg.observerTimeout }

private def mkOrchestratorConfig (cfg : Config) (lens : LensID) : OrchestratorConfig :=
  let base : OrchestratorConfig :=
    { currentLens := lens
      maxLaneChanges := 0
      lensBudget := 1
      decodeTopK := max 1 cfg.maxBranches
      useMultiwayGD := true
      maxMacroSteps := max 1 cfg.macroSteps
      useStructuralInjection := true
      enableTacticDiversification := true
      diversityTopK := max 1 cfg.maxBranches }
  if cfg.expandFallbacks then
    { base with
      decodeTopK := max 12 base.decodeTopK
      diversityTopK := max 12 base.diversityTopK }
  else
    base

private def runStandard (cfg : Config) (goal : String) : IO LensSearchResult := do
  let encoded := encodeGoal goal cfg.currentLens [] none
  let searchCfg := mkSearchConfig cfg
  let baseCfg := mkOrchestratorConfig cfg cfg.currentLens
  let startedMs ← IO.monoMsNow
  let (proved, proof, nodes) ←
    searchInLensWithGoalExpr cfg.currentLens goal encoded.initial searchCfg baseCfg
  let doneMs ← IO.monoMsNow
  pure {
    proved := proved
    proofLens := if proved then some cfg.currentLens else none
    proofScript := proof
    backTransportCertified := proved
    nodesExplored := nodes
    nodesPerLens := [(cfg.currentLens, nodes)]
    transitionPath := if proved then [cfg.currentLens] else []
    wallMs := doneMs - startedMs
  }

private def runLensTransport (cfg : Config) (goal : String) : IO LensSearchResult := do
  let encoded := encodeGoal goal cfg.currentLens [] none
  let atpSearchCfg := mkSearchConfig cfg
  let baseCfg := mkOrchestratorConfig cfg cfg.currentLens
  let searchCfg : LensSearchConfig :=
    { startLens := cfg.currentLens
      maxDepthPerLens := cfg.maxDepth
      maxTotalNodes := cfg.maxNodes
      nodesBeforeTransition := cfg.nodesBeforeTransition
      enableLensTransitions := true
      tryOriginalFirst := true }
  lensTransportedSearchWithGoalExpr goal encoded.initial searchCfg atpSearchCfg baseCfg

private def resultToJson (mode : Mode) (goal : String) (res : LensSearchResult) : Json :=
  let proofLensJson :=
    match res.proofLens with
    | some l => Json.str (lensName l)
    | none => Json.null
  let nodesPerLensJson :=
    Json.arr <| (res.nodesPerLens.map (fun row =>
      Json.mkObj
        [ ("lens", Json.str (lensName row.1))
        , ("nodes", Json.num row.2)
        ])).toArray
  let pathJson := Json.arr <| (res.transitionPath.map (fun l => Json.str (lensName l))).toArray
  Json.mkObj
    [ ("mode", Json.str (modeName mode))
    , ("goal", Json.str goal)
    , ("proved", Json.bool res.proved)
    , ("proof_lens", proofLensJson)
    , ("nodes_explored", Json.num res.nodesExplored)
    , ("nodes_per_lens", nodesPerLensJson)
    , ("transition_path", pathJson)
    , ("wall_ms", Json.num res.wallMs)
    ]

def main (argv : List String) : IO UInt32 := do
  try
    let (cfg, wantsHelp) ← parseArgs argv
    if wantsHelp then
      IO.println usage
      return (0 : UInt32)
    let some goal := cfg.goal
      | IO.eprintln "Error: --goal is required"
        return (2 : UInt32)
    let res ←
      match cfg.mode with
      | .standard => runStandard cfg goal
      | .lensTransport => runLensTransport cfg goal
    let payload := resultToJson cfg.mode goal res
    if cfg.jsonOutput then
      IO.println payload.compress
    else
      IO.println s!"lens_transport_bench: mode={modeName cfg.mode} proved={res.proved} nodes={res.nodesExplored} wall_ms={res.wallMs}"
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"Error: {e}"
    return (2 : UInt32)

end LensTransportBenchMain
end CLI
end HeytingLean

open HeytingLean.CLI.LensTransportBenchMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.LensTransportBenchMain.main args
