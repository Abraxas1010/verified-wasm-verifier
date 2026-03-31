import Lean.Data.Json
import HeytingLean.PathIntegral.Adapter
import HeytingLean.CLI.Args

/-!
# `pi_search`

Executable entry point for PathIntegral beam search over the existing ATP goal
encoding surface.
-/

namespace HeytingLean
namespace PathIntegral
namespace Main

open Lean
open HeytingLean.Embeddings
open HeytingLean.PathIntegral.Adapter

structure Config where
  goal : Option String := none
  currentLens : LensID := .omega
  beamWidth : Nat := 8
  expansionFactor : Nat := 4
  initialBeta : Float := 1.0
  schedule : String := "linear"
  annealRate : Float := 0.1
  geometricRatio : Float := 1.1
  logarithmicScale : Float := 1.0
  maxSteps : Nat := 5
  jsonOutput : Bool := false
  deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "pi_search - PathIntegral ATP search harness"
    , ""
    , "Usage:"
    , "  lake exe pi_search -- --goal \"⊢ True\" [options]"
    , ""
    , "Options:"
    , "  --goal <expr>              Goal expression (required)"
    , "  --current-lens <name>      omega|region|graph|clifford|tensor|topology|matula"
    , "  --beam-width <n>           Beam width (default: 8)"
    , "  --expansion-factor <n>     Candidates kept per beam entry (default: 4)"
    , "  --beta <float>             Initial inverse temperature (default: 1.0)"
    , "  --schedule <kind>          linear|geometric|logarithmic (default: linear)"
    , "  --anneal-rate <float>      Linear beta increase per step (default: 0.1)"
    , "  --geometric-ratio <float>  Geometric beta ratio (default: 1.1)"
    , "  --logarithmic-scale <f>    Logarithmic beta scale (default: 1.0)"
    , "  --max-steps <n>            Search depth budget (default: 5)"
    , "  --json                     Print JSON output (default)"
    , "  --help                     Show this message"
    ]

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

private def parseFloat? (s : String) : Option Float :=
  match Json.parse s.trim with
  | .ok (.num n) => some n.toFloat
  | .error _ => none
  | _ => none

private def floatJson (f : Float) : Json :=
  match Json.parse (toString f) with
  | .ok j => j
  | .error _ => Json.str (toString f)

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) := do
  match args with
  | [] => pure ({ cfg with jsonOutput := true }, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--json" :: rest => parseArgs rest { cfg with jsonOutput := true }
  | "--goal" :: goal :: rest => parseArgs rest { cfg with goal := some goal }
  | "--current-lens" :: lens :: rest =>
      match parseLens? lens with
      | some l => parseArgs rest { cfg with currentLens := l }
      | none => throw <| IO.userError s!"invalid lens: {lens}"
  | "--beam-width" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with beamWidth := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --beam-width: {n}"
  | "--expansion-factor" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with expansionFactor := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --expansion-factor: {n}"
  | "--beta" :: n :: rest =>
      match parseFloat? n with
      | some v => parseArgs rest { cfg with initialBeta := v }
      | none => throw <| IO.userError s!"invalid float for --beta: {n}"
  | "--schedule" :: kind :: rest =>
      match kind.trim.toLower with
      | "linear" | "geometric" | "logarithmic" =>
          parseArgs rest { cfg with schedule := kind.trim.toLower }
      | _ => throw <| IO.userError s!"invalid schedule: {kind}"
  | "--anneal-rate" :: n :: rest =>
      match parseFloat? n with
      | some v => parseArgs rest { cfg with annealRate := v }
      | none => throw <| IO.userError s!"invalid float for --anneal-rate: {n}"
  | "--geometric-ratio" :: n :: rest =>
      match parseFloat? n with
      | some v => parseArgs rest { cfg with geometricRatio := v }
      | none => throw <| IO.userError s!"invalid float for --geometric-ratio: {n}"
  | "--logarithmic-scale" :: n :: rest =>
      match parseFloat? n with
      | some v => parseArgs rest { cfg with logarithmicScale := v }
      | none => throw <| IO.userError s!"invalid float for --logarithmic-scale: {n}"
  | "--max-steps" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with maxSteps := max 1 v }
      | none => throw <| IO.userError s!"invalid nat for --max-steps: {n}"
  | x :: _ => throw <| IO.userError s!"unknown argument: {x}"

private def lensName : LensID → String
  | .omega => "omega"
  | .region => "region"
  | .graph => "graph"
  | .clifford => "clifford"
  | .tensor => "tensor"
  | .topology => "topology"
  | .matula => "matula"

private def scriptJson (rows : List (String × String)) : Json :=
  Json.arr <| rows.toArray.map (fun row =>
    Json.mkObj [("goal", Json.str row.1), ("tactic", Json.str row.2)])

private def scheduleJson (cfg : Config) : Json :=
  match cfg.schedule with
  | "linear" =>
      Json.mkObj [("kind", Json.str "linear"), ("anneal_rate", floatJson cfg.annealRate)]
  | "geometric" =>
      Json.mkObj [("kind", Json.str "geometric"), ("geometric_ratio", floatJson cfg.geometricRatio)]
  | _ =>
      Json.mkObj [("kind", Json.str "logarithmic"), ("logarithmic_scale", floatJson cfg.logarithmicScale)]

private def resultJson
    (cfg : Config)
    (goal : String)
    (result? : Option SearchResult) : Json :=
  match result? with
  | some result =>
      let script := proofPathToScript result.path
      Json.mkObj
        [ ("status", Json.str "found")
        , ("proved", Json.bool true)
        , ("goal", Json.str goal)
        , ("current_lens", Json.str (lensName cfg.currentLens))
        , ("schedule", scheduleJson cfg)
        , ("proof_script", scriptJson script)
        , ("path_weight", floatJson (pathWeightFloat result.finalBeta result.path))
        , ("final_beta", floatJson result.finalBeta)
        , ("steps", Json.num result.path.length)
        , ("search_steps", Json.num result.finalStep)
        , ("reason", Json.str "path_found")
        ]
  | none =>
      Json.mkObj
        [ ("status", Json.str "not_found")
        , ("proved", Json.bool false)
        , ("goal", Json.str goal)
        , ("current_lens", Json.str (lensName cfg.currentLens))
        , ("schedule", scheduleJson cfg)
        , ("proof_script", Json.arr #[])
        , ("path_weight", Json.null)
        , ("final_beta", Json.null)
        , ("steps", Json.num 0)
        , ("search_steps", Json.num 0)
        , ("reason", Json.str "queue_exhausted")
        ]

private def runSearchResult (goal : String) (lens : LensID)
    (cfg : HeytingLean.PathIntegral.SearchConfig) : Option SearchResult :=
  let initial := searchNodeToProofState
    { goal := goal
      depth := 0
      parentTactic := none
      preferredTactic := none
      groupId := none
      groupSubgoalIndex := none
      priorityScore := 0
      proofScriptRev := []
      carry := none }
    lens
  pathIntegralSearchResult cfg initial
    HeytingLean.ATP.DifferentiableATP.sheafTransport standardConstructors standardGoalClosed

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
          return (2 : UInt32)
    let schedule :=
      match cfg.schedule with
      | "linear" => AnnealingSchedule.linear cfg.annealRate
      | "geometric" => AnnealingSchedule.geometric cfg.geometricRatio
      | "logarithmic" => AnnealingSchedule.logarithmic cfg.logarithmicScale
      | _ => AnnealingSchedule.linear cfg.annealRate
    let searchCfg : HeytingLean.PathIntegral.SearchConfig :=
      { beamWidth := cfg.beamWidth
        expansionFactor := cfg.expansionFactor
        initialBeta := cfg.initialBeta
        schedule := schedule
        maxSteps := cfg.maxSteps }
    let result? := runSearchResult goal cfg.currentLens searchCfg
    let result := resultJson cfg goal result?
    if cfg.jsonOutput then
      IO.println result.compress
    else
      IO.println result.pretty
    pure <| if result?.isSome then (0 : UInt32) else (1 : UInt32)
  catch e =>
    IO.eprintln s!"Error: {e}"
    pure (2 : UInt32)

end Main
end PathIntegral
end HeytingLean

open HeytingLean.PathIntegral.Main in
def main (args : List String) : IO UInt32 :=
  HeytingLean.PathIntegral.Main.main args
