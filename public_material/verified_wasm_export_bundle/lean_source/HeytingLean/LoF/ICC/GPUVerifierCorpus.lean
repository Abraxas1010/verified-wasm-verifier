import Lean.Data.Json
import HeytingLean.CLI.VerifierProofCorpus
import HeytingLean.LoF.ICC.GPUVerifierTranslate
import HeytingLean.LoF.ICC.Workloads

namespace HeytingLean
namespace LoF
namespace ICC

open Lean
open HeytingLean.LoF.LoFPrimary

structure CorpusRow where
  sourceWitness : SourceWitness
  expectedAccepted : Bool
  tags : List String := []
  deriving Repr

private def positiveFromSeed (seed : VerifierCorpusSeed) : CorpusRow :=
  { sourceWitness :=
      seed.toSourceWitness
    expectedAccepted := true
    tags := seed.tags ++ ["positive"] }

private def perturbTarget : Expr 0 → Expr 0
  | .void => .mark .void
  | .mark body => .juxt (.mark body) body
  | .juxt lhs rhs => .mark (.juxt lhs rhs)

private theorem perturbTarget_ne (expr : Expr 0) : perturbTarget expr ≠ expr := by
  induction expr with
  | void =>
      simp [perturbTarget]
  | var idx =>
      cases idx.2
  | mark body ih =>
      intro h
      simp [perturbTarget] at h
  | juxt lhs rhs ihL ihR =>
      intro h
      simp [perturbTarget] at h

private def negativeFromSeed (seed : VerifierCorpusSeed) : CorpusRow :=
  let wrongTarget := perturbTarget seed.target
  { sourceWitness :=
      { sourceId := s!"{seed.sourceId}_wrong_target"
        law := seed.law
        source := seed.source
        target := wrongTarget
        provenance := s!"negative companion row for {seed.skyDeclName}"
        sourceFamily := seed.sourceFamily
        sourceModuleName? := some seed.sourceModuleName
        sourceDeclName? := some seed.sourceDeclName
        commonSourceId? := some (mkCommonSourceId seed.sourceModuleName seed.sourceDeclName)
        proofGraphModuleName? := some seed.sourceModuleName
        proofGraphDeclName? := some seed.sourceDeclName
        skyModuleName? := some seed.skyModuleName
        skyDeclName? := some seed.skyDeclName
        tags := seed.tags ++ ["negative"] }
    expectedAccepted := false
    tags := seed.tags ++ ["negative"] }

private def declarationBackedSeeds : List VerifierCorpusSeed :=
  HeytingLean.CLI.VerifierFixture.iccVerifierCorpusSeeds ++
    HeytingLean.CLI.VerifierProofCorpus.iccVerifierCorpusSeeds

def generatedCorpus : List CorpusRow :=
  declarationBackedSeeds.foldr
    (fun seed rows => positiveFromSeed seed :: negativeFromSeed seed :: rows)
    []

def corpusWitnessRows : List (CorpusRow × Except String ICCVerifierWitness) :=
  generatedCorpus.map (fun row => (row, translateVerifierWitness row.sourceWitness))

private def lawString : WitnessLaw → String
  | .calling => "calling"
  | .crossing => "crossing"

private def exprJson : Expr 0 → Json
  | .void => Json.mkObj [("tag", Json.str "void")]
  | .var idx => nomatch idx
  | .mark body => Json.mkObj [("tag", Json.str "mark"), ("value", exprJson body)]
  | .juxt lhs rhs =>
      Json.mkObj [("tag", Json.str "juxt"), ("value", Json.arr #[exprJson lhs, exprJson rhs])]

private def acceptsBool (witness : ICCVerifierWitness) : Bool :=
  decide (step? witness.certificate = some witness.expected) && witness.expected.annFree

private def meaningBool (src : SourceWitness) : Bool :=
  match actualTarget? src.law src.source with
  | some actualTarget => decide (actualTarget = src.target)
  | none => false

private def witnessJson (row : CorpusRow) (witness : ICCVerifierWitness) : Json :=
  let accepted := acceptsBool witness
  let meaningHolds := meaningBool row.sourceWitness
  Json.mkObj
    [ ("source_id", Json.str row.sourceWitness.sourceId)
    , ("law", Json.str (lawString row.sourceWitness.law))
    , ("source", exprJson row.sourceWitness.source)
    , ("target", exprJson row.sourceWitness.target)
    , ("actual_target", exprJson witness.actualTarget)
    , ("certificate", termJson witness.certificate)
    , ("expected", termJson witness.expected)
    , ("expected_ann_free", Json.bool witness.expected.annFree)
    , ("expected_accepted", Json.bool row.expectedAccepted)
    , ("accepted_in_lean", Json.bool accepted)
    , ("meaning_holds", Json.bool meaningHolds)
    , ("translation_tag", Json.str witness.translationTag)
    , ("provenance", Json.str row.sourceWitness.provenance)
    , ("source_family", Json.str row.sourceWitness.sourceFamily)
    , ("source_module_name", row.sourceWitness.sourceModuleName?.map Json.str |>.getD Json.null)
    , ("source_decl_name", row.sourceWitness.sourceDeclName?.map Json.str |>.getD Json.null)
    , ("common_source_id", row.sourceWitness.commonSourceId?.map Json.str |>.getD Json.null)
    , ("proof_graph_module_name", row.sourceWitness.proofGraphModuleName?.map Json.str |>.getD Json.null)
    , ("proof_graph_decl_name", row.sourceWitness.proofGraphDeclName?.map Json.str |>.getD Json.null)
    , ("sky_module_name", row.sourceWitness.skyModuleName?.map Json.str |>.getD Json.null)
    , ("sky_decl_name", row.sourceWitness.skyDeclName?.map Json.str |>.getD Json.null)
    , ("tags", Json.arr <| row.tags.map Json.str |>.toArray)
    ]

private def failureJson (row : CorpusRow) (err : String) : Json :=
  Json.mkObj
    [ ("source_id", Json.str row.sourceWitness.sourceId)
    , ("law", Json.str (lawString row.sourceWitness.law))
    , ("source", exprJson row.sourceWitness.source)
    , ("target", exprJson row.sourceWitness.target)
    , ("expected_accepted", Json.bool row.expectedAccepted)
    , ("accepted_in_lean", Json.bool false)
    , ("meaning_holds", Json.bool false)
    , ("translation_error", Json.str err)
    , ("provenance", Json.str row.sourceWitness.provenance)
    , ("source_family", Json.str row.sourceWitness.sourceFamily)
    , ("source_module_name", row.sourceWitness.sourceModuleName?.map Json.str |>.getD Json.null)
    , ("source_decl_name", row.sourceWitness.sourceDeclName?.map Json.str |>.getD Json.null)
    , ("common_source_id", row.sourceWitness.commonSourceId?.map Json.str |>.getD Json.null)
    , ("proof_graph_module_name", row.sourceWitness.proofGraphModuleName?.map Json.str |>.getD Json.null)
    , ("proof_graph_decl_name", row.sourceWitness.proofGraphDeclName?.map Json.str |>.getD Json.null)
    , ("sky_module_name", row.sourceWitness.skyModuleName?.map Json.str |>.getD Json.null)
    , ("sky_decl_name", row.sourceWitness.skyDeclName?.map Json.str |>.getD Json.null)
    , ("tags", Json.arr <| row.tags.map Json.str |>.toArray)
    ]

def corpusReportJson : Json :=
  Json.mkObj
    [ ("schema", Json.str "icc_gpu_verifier_corpus_v2")
    , ("kind", Json.str "icc_gpu_verifier_generated_corpus")
    , ("honest_boundary", Json.str
        "Generated verifier corpus over the current calling/crossing law surface. This is a declaration-backed source-witness generator over per-module verifier seed catalogs in the local source schema, with explicit common-source and proof-graph identity fields for later cross-surface attachment. It is not a full arbitrary Lean proof-term extractor.")
    , ("rows", Json.arr <|
        corpusWitnessRows.map (fun
          | (row, .ok witness) => witnessJson row witness
          | (row, .error err) => failureJson row err) |>.toArray)
    ]

end ICC
end LoF
end HeytingLean
