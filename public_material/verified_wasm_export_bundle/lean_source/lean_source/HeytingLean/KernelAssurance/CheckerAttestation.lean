import Lean.Data.Json
import HeytingLean.KernelAssurance.ObligationManifest

namespace HeytingLean.KernelAssurance

open Lean

structure CheckerAttestation where
  version : String := "kernel-obligation-checker-attestation-v1"
  checkerModule : String
  checkerKind : String
  sourceBundleDigest : String
  sourceModule : String
  obligationsChecked : Nat
  obligationsPassed : Nat
  obligationsFailed : Nat
  semanticCheckPerformed : Bool
  attested : Bool
  claimBoundary : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def mkCheckerClaimBoundary (checkerModule : String) (semanticCheck : Bool) : String :=
  let semanticNote :=
    if semanticCheck then
      "Semantic verification was performed: the checker replayed kernel operations through an independent implementation."
    else
      "Only structural verification was performed (digest and metadata checking)."
  s!"This checker attestation records that obligations were verified by {checkerModule}. " ++
  semanticNote ++
  " It does not by itself prove Lean's full kernel."

def CheckerAttestation.ofBase
    (base : KernelObligationAssuranceManifest) : CheckerAttestation :=
  let semanticCheck := base.checker.checked > 0 && base.checker.failed = 0
  let claimBoundary := mkCheckerClaimBoundary
    "HeytingLean.CLI.VerifiedCheck" semanticCheck
  { checkerModule := "HeytingLean.CLI.VerifiedCheck"
    checkerKind := "lean4lean_sky_independent"
    sourceBundleDigest := base.bundleDigest
    sourceModule := base.descriptor.moduleName
    obligationsChecked := base.checker.checked
    obligationsPassed := base.checker.passed
    obligationsFailed := base.checker.failed
    semanticCheckPerformed := semanticCheck
    attested := semanticCheck && base.replay.failed = 0
    claimBoundary := claimBoundary }

end HeytingLean.KernelAssurance
