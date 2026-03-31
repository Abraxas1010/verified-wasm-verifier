import Lean.Data.Json
import HeytingLean.LoF.ICC.GPUVerifierTranslate

namespace HeytingLean
namespace LoF
namespace ICC
namespace Encoder

open Lean
open HeytingLean.LoF.LoFPrimary

structure EncodedWitnessCase where
  sourceId : String
  law : String
  expectedAccepted : Bool
  acceptedInLean : Bool
  meaningHolds : Bool
  translationTag? : Option String
  translationError? : Option String
  sourceNodeCount : Nat
  targetNodeCount : Nat
  actualTargetNodeCount? : Option Nat
  certificateNodeCount? : Option Nat
  expectedNodeCount? : Option Nat
  payloadAnnFree : Bool
  preNormalizationConsistent : Bool
  sizeRatio? : Option Float
  deriving Repr

structure EncodedSeedPair where
  positive : EncodedWitnessCase
  negative : EncodedWitnessCase
  encodingDivergence : Bool
  deriving Repr

def lawString : WitnessLaw → String
  | .calling => "calling"
  | .crossing => "crossing"

def exprNodeCount : Expr 0 → Nat
  | .void => 1
  | .var idx => nomatch idx
  | .mark body => exprNodeCount body + 1
  | .juxt lhs rhs => exprNodeCount lhs + exprNodeCount rhs + 1

def termNodeCount : Term → Nat
  | .var _ => 1
  | .lam body => termNodeCount body + 1
  | .app fn arg => termNodeCount fn + termNodeCount arg + 1
  | .bridge body => termNodeCount body + 1
  | .ann val typ => termNodeCount val + termNodeCount typ + 1

private def acceptsBool (witness : ICCVerifierWitness) : Bool :=
  decide (step? witness.certificate = some witness.expected) && witness.expected.annFree

private def meaningBool (src : SourceWitness) : Bool :=
  match actualTarget? src.law src.source with
  | some actualTarget => decide (actualTarget = src.target)
  | none => false

private def ratioOf (termNodes exprNodes : Nat) : Option Float :=
  if exprNodes == 0 then
    none
  else
    some (Float.ofNat termNodes / Float.ofNat exprNodes)

private def renderCase (row : SourceWitness) (expectedAccepted : Bool) (result : Except String ICCVerifierWitness) :
    EncodedWitnessCase :=
  match result with
  | .error err =>
      { sourceId := row.sourceId
        law := lawString row.law
        expectedAccepted := expectedAccepted
        acceptedInLean := false
        meaningHolds := false
        translationTag? := none
        translationError? := some err
        sourceNodeCount := exprNodeCount row.source
        targetNodeCount := exprNodeCount row.target
        actualTargetNodeCount? := none
        certificateNodeCount? := none
        expectedNodeCount? := none
        payloadAnnFree := false
        preNormalizationConsistent := false
        sizeRatio? := none }
  | .ok witness =>
      let expectedNodes := termNodeCount witness.expected
      { sourceId := row.sourceId
        law := lawString row.law
        expectedAccepted := expectedAccepted
        acceptedInLean := acceptsBool witness
        meaningHolds := meaningBool row
        translationTag? := some witness.translationTag
        translationError? := none
        sourceNodeCount := exprNodeCount row.source
        targetNodeCount := exprNodeCount row.target
        actualTargetNodeCount? := some (exprNodeCount witness.actualTarget)
        certificateNodeCount? := some (termNodeCount witness.certificate)
        expectedNodeCount? := some expectedNodes
        payloadAnnFree := witness.expected.annFree && witness.certificate.annFree
        preNormalizationConsistent := meaningBool row
        sizeRatio? := ratioOf expectedNodes (exprNodeCount row.source) }

private def perturbTarget : Expr 0 → Expr 0
  | .void => .mark .void
  | .mark body => .juxt (.mark body) body
  | .juxt lhs rhs => .mark (.juxt lhs rhs)

private def negativeWitness (seed : VerifierCorpusSeed) : SourceWitness :=
  { sourceId := s!"{seed.sourceId}_wrong_target"
    law := seed.law
    source := seed.source
    target := perturbTarget seed.target
    provenance := s!"negative companion row for {seed.sourceDeclName}"
    sourceFamily := seed.sourceFamily
    sourceModuleName? := some seed.sourceModuleName
    sourceDeclName? := some seed.sourceDeclName
    commonSourceId? := some (mkCommonSourceId seed.sourceModuleName seed.sourceDeclName)
    proofGraphModuleName? := some seed.sourceModuleName
    proofGraphDeclName? := some seed.sourceDeclName
    skyModuleName? := some seed.skyModuleName
    skyDeclName? := some seed.skyDeclName
    tags := seed.tags ++ ["negative"] }

def encodeSeedPair (seed : VerifierCorpusSeed) : EncodedSeedPair :=
  let positiveWitness := seed.toSourceWitness
  let negative := negativeWitness seed
  let positiveCase := renderCase positiveWitness true (translateVerifierWitness positiveWitness)
  let negativeCase := renderCase negative false (translateVerifierWitness negative)
  let divergence :=
    positiveCase.acceptedInLean != true ||
    positiveCase.meaningHolds != true ||
    negativeCase.acceptedInLean != false ||
    negativeCase.preNormalizationConsistent != false
  { positive := positiveCase
    negative := negativeCase
    encodingDivergence := divergence }

def encodedWitnessCaseJson (payload : EncodedWitnessCase) : Json :=
  Json.mkObj
    [ ("source_id", Json.str payload.sourceId)
    , ("law", Json.str payload.law)
    , ("expected_accepted", Json.bool payload.expectedAccepted)
    , ("accepted_in_lean", Json.bool payload.acceptedInLean)
    , ("meaning_holds", Json.bool payload.meaningHolds)
    , ("translation_tag", payload.translationTag?.map Json.str |>.getD Json.null)
    , ("translation_error", payload.translationError?.map Json.str |>.getD Json.null)
    , ("source_node_count", toJson payload.sourceNodeCount)
    , ("target_node_count", toJson payload.targetNodeCount)
    , ("actual_target_node_count", payload.actualTargetNodeCount?.map toJson |>.getD Json.null)
    , ("certificate_node_count", payload.certificateNodeCount?.map toJson |>.getD Json.null)
    , ("expected_node_count", payload.expectedNodeCount?.map toJson |>.getD Json.null)
    , ("payload_ann_free", Json.bool payload.payloadAnnFree)
    , ("pre_normalization_consistent", Json.bool payload.preNormalizationConsistent)
    , ("size_ratio", payload.sizeRatio?.map toJson |>.getD Json.null)
    ]

end Encoder
end ICC
end LoF
end HeytingLean
