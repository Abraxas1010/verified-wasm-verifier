import HeytingLean.KernelAssurance.Tier

namespace HeytingLean.KernelAssurance

open Lean

structure KernelAssuranceManifest where
  version : String := "kernel-assurance-v1"
  foundationCommitment : String
  rulesRoot : String
  kernelCommitment : String
  bundleDigest : String
  descriptor : SliceDescriptor
  coverage : CoverageReport
  replay : ReplayReport
  checker : CheckerReport
  tierDecision : TierDecision
  claimBoundary : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def KernelAssuranceManifest.ofBundle
    (bundle : SliceBundle)
    (foundationCommitment rulesRoot kernelCommitment : String)
    (requested : AssuranceTier) : KernelAssuranceManifest :=
  let coverage := CoverageReport.ofBundle bundle
  let replay := ReplayReport.ofBundle bundle
  let checker := CheckerReport.ofBundle bundle
  let tierDecision := decideTier requested coverage replay checker
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
