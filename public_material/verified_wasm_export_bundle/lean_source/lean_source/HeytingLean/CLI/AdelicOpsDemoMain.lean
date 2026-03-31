import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.ProgramCalculus.AdelicOpsInstances
import HeytingLean.ProgramCalculus.Instances.LambdaIRBoolNat

/-!
# `adelic_ops_demo`

Small executable harness for `ProgramCalculus.AdelicProgramOps`.

This currently exercises the baseline `trivialAdelicProgramOps` instance on the
LambdaIR Bool/Nat demo language, validating the reconstruction equation on a
single sample input and emitting a compact JSON report.
-/

namespace HeytingLean.CLI.AdelicOpsDemoMain

open Lean
open HeytingLean
open HeytingLean.ProgramCalculus
open HeytingLean.ProgramCalculus.Instances
open HeytingLean.Embeddings

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def depthToJson (d : Depth) : Json :=
  Json.mkObj <|
    [ ("omega",    Json.num (d .omega))
    , ("region",   Json.num (d .region))
    , ("graph",    Json.num (d .graph))
    , ("clifford", Json.num (d .clifford))
    ]

def main (_argv : List String) : IO UInt32 := do
  try
    let ops := trivialAdelicProgramOps lambdaIRBoolNatLanguage

    let a := lambdaIRBoolNatInterp
    let e := lambdaIRBoolNatInterp
    let (q, r) := ops.renormDiv a e
    let recombined := ops.add (ops.mul q e) r

    let sample : lambdaIRBoolNatLanguage.Input := (true, 7)
    let outA : Nat := lambdaIRBoolNatLanguage.eval a sample
    let outRecombined : Nat := lambdaIRBoolNatLanguage.eval recombined sample
    ok (decide (outA = outRecombined)) "adelic_ops_demo: reconstruction check failed"

    let report :=
      Json.mkObj
        [ ("ok", Json.bool true)
        , ("sampleInput", Json.arr #[Json.bool true, Json.num (7 : Nat)])
        , ("outOriginal", Json.num outA)
        , ("outRecombined", Json.num outRecombined)
        , ("depthOriginal", depthToJson (ops.depth a))
        ]
    IO.println report.compress
    pure 0
  catch e =>
    die s!"adelic_ops_demo: FAILED: {e}"

end HeytingLean.CLI.AdelicOpsDemoMain

open HeytingLean.CLI.AdelicOpsDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.AdelicOpsDemoMain.main args
