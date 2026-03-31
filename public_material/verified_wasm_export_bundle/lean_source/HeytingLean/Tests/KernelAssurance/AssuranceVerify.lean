import HeytingLean.Tests.KernelAssurance.ObligationFixture
import HeytingLean.KernelAssurance.ObligationAssuranceVerify

namespace HeytingLean.Tests.KernelAssurance.AssuranceVerify

open Lean
open HeytingLean.KernelAssurance
open HeytingLean.Tests.KernelAssurance

private def baseManifest : KernelObligationAssuranceManifest :=
  KernelObligationAssuranceManifest.ofBundle
    supportedObligationBundle "foundation" "rules" "kernel" .slice_checker_certified

private def receiptInput : ZKReceiptMetadata :=
  { proofSystem := "groth16"
    circuitKind := "checker_acceptance"
    checkerDigest := ""
    bundleDigest := ""
    receiptDigest := "receipt_123"
    publicInputDigest := "public_456"
    verifierDigest := "verifier_789"
    executionClaim := "Declared receipt metadata for checker execution over the supported obligation bundle."
    claimBoundary := "" }

private def receiptManifest : KernelObligationCABZKManifest :=
  KernelObligationCABZKManifest.ofBase baseManifest (some receiptInput)

private def badCheckerDigestManifest : KernelObligationCABZKManifest :=
  { receiptManifest with checkerDigest := "0xdeadbeef" }

private def badTierManifest : KernelObligationCABZKManifest :=
  { receiptManifest with grantedTier := .none }

private def baseReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofBase baseManifest

private def receiptReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK receiptManifest (some baseManifest)

private def badCheckerReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK badCheckerDigestManifest (some baseManifest)

private def badTierReport : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK badTierManifest (some baseManifest)

example : baseReport.ok = true := by
  native_decide

example : baseReport.loweringAttestationPresent = false := by
  native_decide

example : baseReport.checkerAttestationPresent = false := by
  native_decide

example : baseReport.iccBridgeAttestationPresent = false := by
  native_decide

example : receiptReport.ok = true := by
  native_decide

example : receiptReport.assuranceModeConsistent = true := by
  native_decide

example : receiptReport.receiptBoundaryConservative = true := by
  native_decide

example : badCheckerReport.ok = false := by
  native_decide

example : badCheckerReport.checkerDigestMatches = false := by
  native_decide

example : badTierReport.ok = false := by
  native_decide

example : badTierReport.grantedTierMatchesBase = false := by
  native_decide

end HeytingLean.Tests.KernelAssurance.AssuranceVerify
