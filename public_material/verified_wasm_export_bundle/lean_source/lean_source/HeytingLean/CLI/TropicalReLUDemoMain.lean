import Lean.Data.Json
import HeytingLean.Tropical.ReLU

/-!
# `tropical_relu_demo`

Minimal executable harness for the tropical/ReLU bridge.
It avoids noncomputable real arithmetic at runtime, but exercises the types and data plumbing.
-/

namespace HeytingLean.CLI.TropicalReLUDemoMain

open Lean
open HeytingLean.Tropical

def main (_argv : List String) : IO UInt32 := do
  let tp : TropicalPolynomial 1 :=
    { terms :=
        [ { weights := fun _ => 0, bias := 0 }
        , { weights := fun _ => 0, bias := 0 }
        ] }
  let report :=
    Json.mkObj
      [ ("ok", Json.bool true)
      , ("terms", Json.num tp.terms.length)
      , ("note", Json.str "tropical_relu_demo: representation scaffold only")
      ]
  IO.println report.compress
  pure 0

end HeytingLean.CLI.TropicalReLUDemoMain

open HeytingLean.CLI.TropicalReLUDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.TropicalReLUDemoMain.main args

