import HeytingLean.KernelAssurance.ObligationTier

namespace HeytingLean.KernelAssurance

open Lean

structure KernelObligationAssuranceManifest where
  version : String := "kernel-obligation-assurance-v1"
  foundationCommitment : String
  rulesRoot : String
  kernelCommitment : String
  bundleDigest : String
  descriptor : ObligationSliceDescriptor
  coverage : ObligationCoverageReport
  replay : ObligationReplayReport
  checker : ObligationCheckerReport
  tierDecision : TierDecision
  claimBoundary : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def KernelObligationAssuranceManifest.ofBundle
    (bundle : ObligationSliceBundle)
    (foundationCommitment rulesRoot kernelCommitment : String)
    (requested : AssuranceTier)
    (sourcePayload? : Option Json := none) : KernelObligationAssuranceManifest :=
  let coverage := ObligationCoverageReport.ofBundleWithSourcePayload bundle sourcePayload?
  let replay := ObligationReplayReport.ofBundle bundle
  let checker := ObligationCheckerReport.ofBundle bundle
  let tierDecision := decideObligationTier requested coverage replay checker
  {
    foundationCommitment := foundationCommitment
    rulesRoot := rulesRoot
    kernelCommitment := kernelCommitment
    bundleDigest := bundle.bundleDigest
    descriptor := bundle.descriptor
    coverage := coverage
    replay := replay
    checker := checker
    tierDecision := tierDecision
    claimBoundary := bundle.descriptor.claimBoundary
  }

end HeytingLean.KernelAssurance
