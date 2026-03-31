import Lean.Data.Json
import HeytingLean.ProgramCalculus.AdelicOpsInstances.SKYAdelic

/-!
# `adelic_futamura_demo`

Executable harness that exercises a non-trivial `AdelicProgramOps` instance (SKY) and emits a
depth-additivity check as JSON.
-/

namespace HeytingLean.CLI.AdelicFutamuraDemoMain

open Lean
open HeytingLean
open HeytingLean.Embeddings
open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.ProgramCalculus
open HeytingLean.ProgramCalculus.AdelicOpsInstances

private def depthToJson (d : Depth) : Json :=
  Json.mkObj <|
    [ ("omega",    Json.num (d .omega))
    , ("region",   Json.num (d .region))
    , ("graph",    Json.num (d .graph))
    , ("clifford", Json.num (d .clifford))
    ]

def main (_argv : List String) : IO UInt32 := do
  let ops := skyAdelicProgramOps 100

  let a : Comb := .S
  let b : Comb := .K
  let ab := ops.mul a b

  let okMul :=
    decide (ops.depth ab .omega = ops.depth a .omega + ops.depth b .omega) &&
    decide (ops.depth ab .region = ops.depth a .region + ops.depth b .region) &&
    decide (ops.depth ab .graph = ops.depth a .graph + ops.depth b .graph) &&
    decide (ops.depth ab .clifford = ops.depth a .clifford + ops.depth b .clifford)

  let report :=
    Json.mkObj
      [ ("ok", Json.bool okMul)
      , ("depthA", depthToJson (ops.depth a))
      , ("depthB", depthToJson (ops.depth b))
      , ("depthAB", depthToJson (ops.depth ab))
      ]
  IO.println report.compress
  pure (if okMul then 0 else 1)

end HeytingLean.CLI.AdelicFutamuraDemoMain

open HeytingLean.CLI.AdelicFutamuraDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.AdelicFutamuraDemoMain.main args
