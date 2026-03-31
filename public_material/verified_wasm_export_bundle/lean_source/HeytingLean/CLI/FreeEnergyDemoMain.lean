import Lean.Data.Json
import HeytingLean.ActiveInference.FreeEnergy

/-!
# `free_energy_demo`

Minimal executable harness for the Active Inference / Free Energy scaffolding.
This is intentionally “data-only”: it constructs small models and emits a JSON marker.
-/

namespace HeytingLean.CLI.FreeEnergyDemoMain

open Lean
open HeytingLean.ActiveInference

def main (_argv : List String) : IO UInt32 := do
  let _gen : GenerativeModel Bool Bool :=
    { prior := fun _ => 1
      likelihood := fun _ _ => 1 }
  let _rec : RecognitionModel Bool Bool :=
    { posterior := fun _ _ => 1 }
  let report :=
    Json.mkObj
      [ ("ok", Json.bool true)
      , ("note", Json.str "free_energy_demo: objective scaffold only")
      ]
  IO.println report.compress
  pure 0

end HeytingLean.CLI.FreeEnergyDemoMain

open HeytingLean.CLI.FreeEnergyDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FreeEnergyDemoMain.main args

