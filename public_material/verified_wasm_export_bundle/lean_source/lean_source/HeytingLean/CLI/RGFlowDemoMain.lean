import Lean.Data.Json
import HeytingLean.Renormalization.CoarseGrain

/-!
# `rg_flow_demo`

Executable harness for the renormalization-group flow scaffolding.

This demo is fully computable: it operates on `Nat`-tagged scales and prints a small JSON report.
-/

namespace HeytingLean.CLI.RGFlowDemoMain

open Lean
open HeytingLean.Renormalization

private def predRG : RGTransform Nat :=
  { coarsen := fun s => { resolution := s.resolution.pred, representation := s.representation }
    resolution_decreases := by
      intro s
      cases s.resolution with
      | zero =>
          exact Or.inr rfl
      | succ n =>
          exact Or.inl (Nat.pred_lt (Nat.succ_ne_zero n)) }

def main (_argv : List String) : IO UInt32 := do
  let drg : DeepRG Nat := { layers := [predRG, predRG, predRG] }
  let initial : Scale Nat := { resolution := 3, representation := 42 }
  let final := drg.flow initial
  let report :=
    Json.mkObj
      [ ("ok", Json.bool true)
      , ("initialResolution", Json.num initial.resolution)
      , ("finalResolution", Json.num final.resolution)
      ]
  IO.println report.compress
  pure 0

end HeytingLean.CLI.RGFlowDemoMain

open HeytingLean.CLI.RGFlowDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.RGFlowDemoMain.main args
