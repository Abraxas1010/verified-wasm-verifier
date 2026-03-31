import Lean.Data.Json
import HeytingLean.LoF.ICC.WitnessSpec
import HeytingLean.LoF.ICC.Workloads

namespace HeytingLean
namespace LoF
namespace ICC

open Lean
open HeytingLean.LoF.LoFPrimary

private def lawString : WitnessLaw → String
  | .calling => "calling"
  | .crossing => "crossing"

private def exprJson : Expr 0 → Json
  | .void => Json.mkObj [("tag", Json.str "void")]
  | .var idx => nomatch idx
  | .mark body => Json.mkObj [("tag", Json.str "mark"), ("value", exprJson body)]
  | .juxt lhs rhs =>
      Json.mkObj [("tag", Json.str "juxt"), ("value", Json.arr #[exprJson lhs, exprJson rhs])]

def witnessEntryJson (entry : WitnessEntry) : Json :=
  Json.mkObj
    [ ("rule_type", Json.num (witnessRuleTypeCode entry.ruleType))
    , ("left_agent", Json.num entry.leftAgent.toNat)
    , ("right_agent", Json.num entry.rightAgent.toNat)
    ]

def canonicalWitnessJson (row : ICCCanonicalWitness) : Json :=
  Json.mkObj
    [ ("source_id", Json.str row.sourceId)
    , ("law", Json.str (lawString row.law))
    , ("source", exprJson row.source)
    , ("target", exprJson row.target)
    , ("actual_target", exprJson row.actualTarget)
    , ("certificate", termJson row.certificate)
    , ("normalized", termJson row.normalized)
    , ("expected", termJson row.expected)
    , ("expected_accepted", Json.bool row.expectedAccepted)
    , ("accepted_in_lean", Json.bool row.acceptedInLean)
    , ("meaning_holds", Json.bool row.meaningHolds)
    , ("normalized_ann_free", Json.bool row.normalized.annFree)
    , ("translation_tag", Json.str row.translationTag)
    , ("provenance", Json.str row.provenance)
    , ("source_family", Json.str row.sourceFamily)
    , ("source_module_name", row.sourceModuleName?.map Json.str |>.getD Json.null)
    , ("source_decl_name", row.sourceDeclName?.map Json.str |>.getD Json.null)
    , ("common_source_id", row.commonSourceId?.map Json.str |>.getD Json.null)
    , ("proof_graph_module_name", row.proofGraphModuleName?.map Json.str |>.getD Json.null)
    , ("proof_graph_decl_name", row.proofGraphDeclName?.map Json.str |>.getD Json.null)
    , ("sky_module_name", row.skyModuleName?.map Json.str |>.getD Json.null)
    , ("sky_decl_name", row.skyDeclName?.map Json.str |>.getD Json.null)
    , ("tags", Json.arr <| row.tags.map Json.str |>.toArray)
    , ("witness", Json.arr <| row.witness.map witnessEntryJson |>.toArray)
    ]

def canonicalWitnessBundleJson (rows : List ICCCanonicalWitness) : Json :=
  Json.mkObj
    [ ("schema", Json.str "icc_canonical_witness_bundle_v1")
    , ("kind", Json.str "icc_canonical_witness_bundle")
    , ("honest_boundary", Json.str
        "Canonical replay witnesses over the current ICC verifier corpus. Each row carries the original declaration provenance plus a deterministic replay trace over the current Lean/Rust ICC stepper. This is still local corpus evidence, not an arbitrary proof-term extractor.")
    , ("rows", Json.arr <| rows.map canonicalWitnessJson |>.toArray)
    ]

end ICC
end LoF
end HeytingLean
