import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICC.GPUVerifier
import HeytingLean.LoF.ICC.Workloads

open Lean

namespace HeytingLean.CLI.ICCGPUVerifierFixtureMain

open HeytingLean.LoF
open HeytingLean.LoF.ICC
open HeytingLean.LoF.LoFPrimary

private def lawString : WitnessLaw → String
  | .calling => "calling"
  | .crossing => "crossing"

private def exprJson : LoFPrimary.Expr 0 → Json
  | .void =>
      Json.mkObj [("tag", Json.str "void")]
  | .var idx =>
      nomatch idx
  | .mark body =>
      Json.mkObj [("tag", Json.str "mark"), ("value", exprJson body)]
  | .juxt lhs rhs =>
      Json.mkObj
        [ ("tag", Json.str "juxt")
        , ("value", Json.arr #[exprJson lhs, exprJson rhs])
        ]

private def witnessJson (name : String) (witness : TinyLawWitness) : Json :=
  Json.mkObj
    [ ("name", Json.str name)
    , ("source_id", Json.str witness.sourceId)
    , ("law", Json.str (lawString witness.law))
    , ("source", exprJson witness.source)
    , ("target", exprJson witness.target)
    , ("actual_target", exprJson witness.actualTarget)
    , ("certificate", termJson witness.certificate)
    , ("expected", termJson witness.expected)
    , ("expected_ann_free", Json.bool witness.expected.annFree)
    , ("proof_status", Json.str "proved_in_lean_fixture_module")
    , ("translation_tag", Json.str witness.translationTag)
    , ("provenance", Json.str witness.provenance)
    ]

def reportJson : Json :=
  Json.mkObj
    [ ("schema", Json.str "icc_gpu_verifier_seed_v1")
    , ("kind", Json.str "icc_gpu_verifier_seed_fragment")
    , ("honest_boundary", Json.str
        "Tiny calling/crossing seed witnesses over existing ICC reductions; not a full LoF proof extractor or general GPU type checker.")
    , ("cases", Json.arr <| witnessFixtures.map (fun (name, witness) => witnessJson name witness) |>.toArray)
    ]

def main (_args : List String) : IO UInt32 := do
  IO.println reportJson.compress
  pure 0

end HeytingLean.CLI.ICCGPUVerifierFixtureMain

def main := HeytingLean.CLI.ICCGPUVerifierFixtureMain.main
