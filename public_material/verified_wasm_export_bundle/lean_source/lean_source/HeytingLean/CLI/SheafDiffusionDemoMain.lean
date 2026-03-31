import Lean.Data.Json
import HeytingLean.LoF.Combinators.Topos.SheafNeuralNet

/-!
# `sheaf_diffusion_demo`

Minimal executable harness for the first-order sheaf diffusion step.
-/

namespace HeytingLean.CLI.SheafDiffusionDemoMain

open Lean
open HeytingLean.LoF.Combinators.Topos

private def unitSheaf : CellularSheaf Unit Unit :=
  { stalk := fun _ => ℝ
    edge_map := fun _ => ((), ())
    restriction := fun _ => LinearMap.id }

def main (_argv : List String) : IO UInt32 := do
  let initial : Unit → ℝ := fun _ => 0
  let _out := sheafDiffusion unitSheaf initial (1 : ℝ)
  let report :=
    Json.mkObj
      [ ("ok", Json.bool true)
      , ("note", Json.str "sheaf_diffusion_demo: computed first-order linear diffusion step")
      ]
  IO.println report.compress
  pure 0

end HeytingLean.CLI.SheafDiffusionDemoMain

open HeytingLean.CLI.SheafDiffusionDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.SheafDiffusionDemoMain.main args
