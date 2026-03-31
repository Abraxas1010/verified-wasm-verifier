import Lean.Data.Json
import HeytingLean.LoF.ICC.Encoder.DirectLower
import HeytingLean.LoF.ICC.Encoder.ICCEnvironment
import HeytingLean.LoF.ICC.Encoder.SemanticGate
import HeytingLean.LoF.ICC.Encoder.Translate

namespace HeytingLean
namespace LoF
namespace ICC
namespace Encoder

open Lean

structure EncoderAnnotatedRow where
  summary : DeclSummary
  classification : DeclClassification
  envSummary : ICCEnvironmentSummary
  directLowering : DirectLoweringAttempt
  semanticGate : SemanticGateAttempt
  encoded? : Option EncodedSeedPair := none
  classifierBug : Bool := false
  deriving Repr

private def promotedClassification
    (summary : DeclSummary)
    (classification : DeclClassification)
    (directLowering : DirectLoweringAttempt)
    (semanticGate : SemanticGateAttempt) : DeclClassification :=
  if classification.exactCatalogMatch || classification.aggregateCatalogMatch then
    classification
  else if semanticGate.status == .success then
    { tier := .tierA
      reason := "staged_kernel_semantic_exec"
      detail := s!"{summary.declName} is fully ingested through direct declaration-body staging plus executable staged-kernel inference/checking against its declaration type."
      hasAxiomDeps := classification.hasAxiomDeps
      hasOpaqueDeps := classification.hasOpaqueDeps
      hasRecursorDeps := classification.hasRecursorDeps
      trustAssumptions := (classification.trustAssumptions ++ semanticGate.trustAssumptions).eraseDups }
  else if directLowering.status == .success then
    { tier := .tierA
      reason := "direct_decl_body_staging"
      detail := s!"{summary.declName} is fully ingested through direct staged lowering of its declaration type and value/proof body into the kernel-expression execution plane."
      hasAxiomDeps := classification.hasAxiomDeps
      hasOpaqueDeps := classification.hasOpaqueDeps
      hasRecursorDeps := classification.hasRecursorDeps
      trustAssumptions := (classification.trustAssumptions ++ directLowering.trustAssumptions).eraseDups }
  else
    classification

def annotateDecl
    (env : Environment)
    (declName : Name)
    (ci : ConstantInfo)
    (maxConsts : Nat := 512)
    (maxNodes : Nat := 200000) : IO EncoderAnnotatedRow := do
  IO.eprintln s!"[annotateDecl] summarize {declName}"
  let summary := summarizeDecl env declName ci maxConsts
  IO.eprintln s!"[annotateDecl] classify {declName}"
  let baseClassification := classifyDecl env summary
  IO.eprintln s!"[annotateDecl] directLowering {declName}"
  let directLowering ← directLoweringAttempt env summary ci maxNodes
  IO.eprintln s!"[annotateDecl] semanticGate {declName}"
  let semanticGate ← semanticGateAttempt env summary ci maxConsts
  IO.eprintln s!"[annotateDecl] finalize {declName}"
  let classification := promotedClassification summary baseClassification directLowering semanticGate
  let envSummary := summarizeICCEnvironment env summary classification
  let encoded? := classification.supportedSeed?.map encodeSeedPair
  let classifierBug :=
    classification.tier == .tierA &&
      encoded?.isNone &&
      !classification.aggregateCatalogMatch &&
      directLowering.status != .success
  pure
    { summary := summary
      classification := classification
      envSummary := envSummary
      directLowering := directLowering
      semanticGate := semanticGate
      encoded? := encoded?
      classifierBug := classifierBug }

def annotatedRowJson (row : EncoderAnnotatedRow) : Json :=
  let moduleName := row.summary.moduleName.toString
  let declName := row.summary.declName.toString
  let supportedSeed? := row.classification.supportedSeed?
  let directSuccess := row.directLowering.status == .success
  let semanticSuccess := row.semanticGate.status == .success
  let encodingPlane :=
    match row.encoded?, semanticSuccess, directSuccess, row.classification.aggregateCatalogMatch with
    | some _, _, _, _ => Json.str "seed_witness_pair"
    | none, true, _, _ => Json.str "staged_kernel_semantic_exec"
    | none, false, true, _ => Json.str "direct_decl_body_staging"
    | none, false, false, true => Json.str "aggregate_seed_catalog"
    | none, false, false, false => Json.null
  let ingestionStatus :=
    match row.encoded? with
    | some _ => "full_ingestion"
    | none =>
        if semanticSuccess || directSuccess || row.classification.aggregateCatalogMatch then
          "full_ingestion"
        else match row.classification.tier with
        | .tierA => "classifier_bug"
        | .tierB => "partial_ingestion"
        | .tierC => "boundary_ingestion"
  let encodingDivergence := row.encoded?.map (·.encodingDivergence) |>.getD false
  Json.mkObj
    [ ("module_name", Json.str moduleName)
    , ("decl_name", Json.str declName)
    , ("decl_kind", Json.str row.summary.declKind)
    , ("proof_body_visible", Json.bool row.summary.proofBodyVisible)
    , ("tier", Json.str row.classification.tier.code)
    , ("classification_reason", Json.str row.classification.reason)
    , ("classification_detail", Json.str row.classification.detail)
    , ("ingestion_status", Json.str ingestionStatus)
    , ("encoding_plane", encodingPlane)
    , ("exact_catalog_match", Json.bool row.classification.exactCatalogMatch)
    , ("aggregate_seed_catalog_match", Json.bool row.classification.aggregateCatalogMatch)
    , ("supported_source_id", supportedSeed?.map (fun seed => Json.str seed.sourceId) |>.getD Json.null)
    , ("common_source_id", supportedSeed?.map (fun seed => Json.str (mkCommonSourceId seed.sourceModuleName seed.sourceDeclName)) |>.getD Json.null)
    , ("source_family", supportedSeed?.map (fun seed => Json.str seed.sourceFamily) |>.getD Json.null)
    , ("tags", Json.arr <| supportedSeed?.map (fun seed => seed.tags.map Json.str |>.toArray) |>.getD #[])
    , ("direct_ref_count", toJson row.summary.directRefs.size)
    , ("direct_refs", Json.arr <| row.summary.directRefs.map (fun n => Json.str n.toString))
    , ("missing_deps", Json.arr <| row.summary.missingDeps.map (fun n => Json.str n.toString))
    , ("icc_environment", iccEnvironmentJson row.envSummary)
    , ("direct_lowering", directLoweringAttemptJson row.directLowering)
    , ("semantic_gate", semanticGateAttemptJson row.semanticGate)
    , ("encoding_divergence", Json.bool encodingDivergence)
    , ("classifier_bug", Json.bool row.classifierBug)
    , ("positive_case", row.encoded?.map (fun payload => encodedWitnessCaseJson payload.positive) |>.getD Json.null)
    , ("negative_case", row.encoded?.map (fun payload => encodedWitnessCaseJson payload.negative) |>.getD Json.null)
    ]

end Encoder
end ICC
end LoF
end HeytingLean
