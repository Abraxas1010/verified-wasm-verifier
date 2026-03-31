import Lean.Data.Json
import HeytingLean.ATP.NodeActivatedLensFrontier

/-!
# `node_activated_lens_frontier`

Small CLI wrapper around the Lean-certified node frontier activation contract.
-/

namespace HeytingLean
namespace CLI
namespace NodeActivatedLensFrontierMain

open Lean
open HeytingLean.ATP

private def usage : String :=
  String.intercalate "\n"
    [ "node_activated_lens_frontier - Lean-certified node frontier activator"
    , ""
    , "Usage:"
    , "  lake exe node_activated_lens_frontier -- --summary-json <path> [--json]"
    , "  lake exe node_activated_lens_frontier -- --summary-payload '<json>' [--json]"
    , ""
    , "Options:"
    , "  --summary-json <path>     Read NodeActivationSummary payload from a JSON file"
    , "  --summary-payload <json>  Read NodeActivationSummary directly from a JSON string"
    , "  --json                    Print machine-readable JSON (default behavior)"
    , "  --help                    Show this message"
    ]

structure Config where
  summaryJson : Option String := none
  summaryPayload : Option String := none
  jsonOutput : Bool := true
  deriving Repr

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) := do
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--json" :: rest => parseArgs rest { cfg with jsonOutput := true }
  | "--summary-json" :: path :: rest => parseArgs rest { cfg with summaryJson := some path }
  | "--summary-payload" :: payload :: rest => parseArgs rest { cfg with summaryPayload := some payload }
  | arg :: _ => throw <| IO.userError s!"unknown argument: {arg}"

private def getObjField (obj : Json) (key : String) : Except String Json := do
  obj.getObjVal? key

private def getStringField (obj : Json) (key : String) : Except String String := do
  (← getObjField obj key).getStr?

private def getNatField (obj : Json) (key : String) : Except String Nat := do
  let n ← (← getObjField obj key).getNat?
  pure n

private def getBoolFieldD (obj : Json) (key : String) (fallback : Bool) : Except String Bool := do
  match obj.getObjVal? key with
  | .ok value => value.getBool?
  | .error _ => pure fallback

private def getStringFieldD (obj : Json) (key : String) (fallback : String) : Except String String := do
  match obj.getObjVal? key with
  | .ok value =>
      match value with
      | .null => pure fallback
      | _ => value.getStr?
  | .error _ => pure fallback

private def getOptStringField (obj : Json) (key : String) : Except String (Option String) := do
  match obj.getObjVal? key with
  | .ok value =>
      match value with
      | .null => pure none
      | _ => return some (← value.getStr?)
  | .error _ => pure none

private def parseLensArray? (obj : Json) (key : String) : Except String (List Embeddings.LensID) := do
  match obj.getObjVal? key with
  | .error _ => pure []
  | .ok value =>
      let arr ← value.getArr?
      let mut out : List Embeddings.LensID := []
      for item in arr do
        let raw ← item.getStr?
        match lensFromString? raw with
        | some l => out := out.concat l
        | none => throw s!"unknown lens: {raw}"
      pure out

private def parseStringArray? (obj : Json) (key : String) : Except String (List String) := do
  match obj.getObjVal? key with
  | .error _ => pure []
  | .ok value =>
      let arr ← value.getArr?
      let mut out : List String := []
      for item in arr do
        out := out.concat (← item.getStr?)
      pure out

private def summaryFromJson (j : Json) : Except String NodeActivationSummary := do
  let nodeId := ← getNatField j "node_id"
  let currentLensRaw := ← getStringField j "current_lens"
  let currentLens ←
    match lensFromString? currentLensRaw with
    | some l => pure l
    | none => throw s!"unknown lens: {currentLensRaw}"
  return {
    nodeId := nodeId
    currentLens := currentLens
    theoremName := ← getStringFieldD j "theorem_name" ""
    transportTargets := ← parseLensArray? j "transport_targets"
    obstructionClass := ← getOptStringField j "obstruction_class"
    suggestedLenses := ← parseLensArray? j "suggested_lenses"
    sheafWitnesses := ← parseStringArray? j "sheaf_witnesses"
    replayScriptPresent := ← getBoolFieldD j "replay_script_present" false
  }

private def loadSummaryJson (cfg : Config) : IO Json := do
  match cfg.summaryPayload, cfg.summaryJson with
  | some payload, _ =>
      match Json.parse payload with
      | .ok j => pure j
      | .error e => throw <| IO.userError s!"invalid summary payload: {e}"
  | none, some path =>
      let raw ← IO.FS.readFile path
      match Json.parse raw with
      | .ok j => pure j
      | .error e => throw <| IO.userError s!"invalid summary JSON file: {e}"
  | none, none =>
      throw <| IO.userError "missing summary input: use --summary-json or --summary-payload"

def mainImpl (args : List String) : IO UInt32 := do
  let (cfg, showHelp) ← parseArgs args
  if showHelp then
    IO.println usage
    return 0
  let summaryJson ← loadSummaryJson cfg
  let summary ←
    match summaryFromJson summaryJson with
    | .ok s => pure s
    | .error e => throw <| IO.userError e
  IO.println <| (activationToJson summary).compress
  return 0

end NodeActivatedLensFrontierMain
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.NodeActivatedLensFrontierMain.mainImpl args
