import HeytingLean.Tests.KernelAssurance.ObligationFixture
import HeytingLean.KernelAssurance.ObligationAssuranceVerify

namespace HeytingLean.Tests.KernelAssurance.CheckerAttestation

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
  let tampered := { CheckerAttestation.ofBase baseManifest with checkerModule := "FakeChecker" }
  { cabManifest with checkerAttestation := some tampered }

private def tamperedReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK tamperedManifest (some baseManifest)

example : cabManifest.checkerAttestation.isSome = true := by
  native_decide

example :
    (cabManifest.checkerAttestation.getD default).checkerModule = "HeytingLean.CLI.VerifiedCheck" := by
  native_decide

example :
    (cabManifest.checkerAttestation.getD default).checkerKind = "lean4lean_sky_independent" := by
  native_decide

example : verifyReport.ok = true := by
  native_decide

example : verifyReport.checkerAttestationPresent = true := by
  native_decide

example : verifyReport.checkerAttestationConsistent = true := by
  native_decide

example : verifyReport.checkerBoundaryConservative = true := by
  native_decide

example : tamperedReport.ok = false := by
  native_decide

example : tamperedReport.checkerAttestationConsistent = false := by
  native_decide

private def missingCheckerManifest : KernelObligationCABZKManifest :=
  { cabManifest with checkerAttestation := none }

private def missingCheckerReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK missingCheckerManifest (some baseManifest)

example : missingCheckerReport.ok = false := by
  native_decide

example : missingCheckerReport.checkerAttestationPresent = false := by
  native_decide

end HeytingLean.Tests.KernelAssurance.CheckerAttestation
