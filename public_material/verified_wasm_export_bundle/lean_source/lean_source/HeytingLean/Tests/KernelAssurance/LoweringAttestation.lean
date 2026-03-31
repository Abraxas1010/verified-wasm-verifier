import HeytingLean.Tests.KernelAssurance.ObligationFixture
import HeytingLean.KernelAssurance.ObligationAssuranceVerify

namespace HeytingLean.Tests.KernelAssurance.LoweringAttestation

open HeytingLean.KernelAssurance
open HeytingLean.Tests.KernelAssurance

private def baseManifest : KernelObligationAssuranceManifest :=
  KernelObligationAssuranceManifest.ofBundle
    supportedObligationBundle "foundation" "rules" "kernel" .slice_checker_certified

private def cabManifest : KernelObligationCABZKManifest :=
  KernelObligationCABZKManifest.ofBase baseManifest

private def verifyReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK cabManifest (some baseManifest)

private def tamperedManifest : KernelObligationCABZKManifest :=
  let tampered := { LoweringAttestation.ofBase baseManifest with claimBoundary := "bad boundary" }
  { cabManifest with loweringAttestation := some tampered }

private def tamperedReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK tamperedManifest (some baseManifest)

example : baseManifest.coverage.loweringFormallyVerified = true := by
  native_decide

example : cabManifest.loweringAttestation.isSome = true := by
  native_decide

example :
    (cabManifest.loweringAttestation.getD default).sourceBundleDigest = baseManifest.bundleDigest := by
  native_decide

example :
    (cabManifest.loweringAttestation.getD default).sourceModule = baseManifest.descriptor.moduleName := by
  native_decide

example : verifyReport.ok = true := by
  native_decide

example : verifyReport.loweringAttestationPresent = true := by
  native_decide

example : verifyReport.loweringAttestationConsistent = true := by
  native_decide

example : verifyReport.loweringBoundaryConservative = true := by
  native_decide

example : tamperedReport.ok = false := by
  native_decide

example : tamperedReport.loweringAttestationConsistent = false := by
  native_decide

private def missingLoweringManifest : KernelObligationCABZKManifest :=
  { cabManifest with loweringAttestation := none }

private def missingLoweringReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK missingLoweringManifest (some baseManifest)

example : missingLoweringReport.ok = false := by
  native_decide

example : missingLoweringReport.loweringAttestationPresent = false := by
  native_decide

end HeytingLean.Tests.KernelAssurance.LoweringAttestation
