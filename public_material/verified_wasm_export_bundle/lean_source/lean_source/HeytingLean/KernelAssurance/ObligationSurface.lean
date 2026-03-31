import Lean.Data.Json
import HeytingLean.KernelAssurance.Surface
import HeytingLean.LoF.LeanKernel.VerifierObligationJson

namespace HeytingLean.KernelAssurance

open Lean
open HeytingLean.LoF.LeanKernel

inductive ObligationFamilyId where
  | whnf
  | infer
  | defeq
  | check
  | unknown
  deriving Repr, Inhabited, BEq, DecidableEq, ToJson, FromJson

instance : ToString ObligationFamilyId where
  toString
    | .whnf => "whnf"
    | .infer => "infer"
    | .defeq => "defeq"
    | .check => "check"
    | .unknown => "unknown"

def allObligationFamilies : Array ObligationFamilyId :=
  #[.whnf, .infer, .defeq, .check, .unknown]

def familyOfVerificationMode : String → ObligationFamilyId
  | "whnf_call" => .whnf
  | "whnf_type" => .whnf
  | "whnf_value" => .whnf
  | "infer_type_sort" => .infer
  | "infer_value_shape" => .infer
  | "infer_value" => .infer
  | "defeq_inferred_declared" => .defeq
  | "check_value" => .check
  | _ => .unknown

def expectedReplayKind? : String → Option ReplayKind
  | "whnf_call" => some .whnfCall
  | "whnf_type" => some .tagCheck
  | "whnf_value" => some .tagCheck
  | "infer_type_sort" => some .tagCheck
  | "infer_value_shape" => some .tagCheck
  | "infer_value" => some .tagCheck
  | "defeq_inferred_declared" => some .tagCheck
  | "check_value" => some .tagCheck
  | _ => none

def familyOfObligation (obligation : VerifierObligation) : ObligationFamilyId :=
  familyOfVerificationMode obligation.verificationMode

def statusOfObligation (obligation : VerifierObligation) : SupportStatus :=
  match expectedReplayKind? obligation.verificationMode with
  | some expected =>
      if obligation.replayKind = expected then .supported else .blocked
  | none =>
      if familyOfObligation obligation = .unknown then .unclassified else .blocked

structure ObligationSliceDescriptor where
  version : String := "kernel-obligation-assurance-v1"
  schemaVersion : Nat := 1
  formatName : String := "sky-v1"
  toolName : String := "verified_check"
  artifactKind : String := "portable_verifier_obligations"
  moduleName : String
  traceGrain : String
  joinStrategy : String
  traceMaxSteps : Nat
  fuelWhnf : Nat
  fuelDefEq : Nat
  fuelReduce : Nat
  maxNodes : Nat
  honestAssessment : String
  claimBoundary : String :=
    "Explicit exported WHNF/DefEq/Infer/Check obligation assurance only; not a proof of Lean's full kernel."
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def mkObligationClaimBoundary (artifact : VerifierArtifact) : String :=
  (if artifact.honestAssessment.isEmpty then
    "Portable verifier obligations only."
  else
    artifact.honestAssessment) ++
    " Explicit exported WHNF/DefEq/Infer/Check obligation assurance only; not a proof of Lean's full kernel."

end HeytingLean.KernelAssurance
