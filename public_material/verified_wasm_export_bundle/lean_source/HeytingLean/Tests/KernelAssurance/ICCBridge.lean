import HeytingLean.Tests.KernelAssurance.ObligationFixture
import HeytingLean.KernelAssurance.ICCBridgeAttestation
import HeytingLean.KernelAssurance.ObligationAssuranceVerify

namespace HeytingLean.Tests.KernelAssurance.ICCBridge

open Lean
open HeytingLean.KernelAssurance
open HeytingLean.Tests.KernelAssurance

private def baseManifest : KernelObligationAssuranceManifest :=
  KernelObligationAssuranceManifest.ofBundle
    sourceScopeBundle "foundation" "rules" "kernel" .slice_checker_certified (some sourceScopePayload)

private def bridgeManifest : KernelObligationICCBridgeManifest :=
  KernelObligationICCBridgeManifest.ofBase
    baseManifest sourceScopeICCExport sourceScopeICCNoLoss (some sourceScopePayload)

private def mismatchManifest : KernelObligationICCBridgeManifest :=
  KernelObligationICCBridgeManifest.ofBase
    baseManifest sourceScopeICCExport sourceScopeICCNoLossMismatch (some sourceScopePayload)

example : bridgeManifest.bridge.sourceBundleDigest = baseManifest.bundleDigest := by
  native_decide

example : bridgeManifest.bridge.sourceModule = "HeytingLean.Tests.KernelAssurance.SourceScope" := by
  native_decide

example : bridgeManifest.bridge.sourceExportedObligations = baseManifest.coverage.exportedObligations := by
  native_decide

example : bridgeManifest.bridge.sourceDiscoveredObligations = baseManifest.coverage.discoveredObligations := by
  native_decide

example : bridgeManifest.bridge.noLossStatus = true := by
  native_decide

example : bridgeManifest.bridge.moduleAlignment = true := by
  native_decide

example : bridgeManifest.bridge.declAlignment = true := by
  native_decide

example : bridgeManifest.bridge.attested = true := by
  native_decide

example : mismatchManifest.bridge.attested = false := by
  native_decide

example : mismatchManifest.bridge.noLossStatus = false := by
  native_decide

example : bridgeManifest.grantedTier = baseManifest.tierDecision.granted := by
  native_decide

example :
    decide ((bridgeManifest.claimBoundary.splitOn
      "does not promote ICC/ICCKernel to the trusted checker").length > 1) := by
  native_decide

-- Verifier integration: ICC bridge in CAB-ZK manifest
private def cabManifest : KernelObligationCABZKManifest :=
  KernelObligationCABZKManifest.ofBase baseManifest

private def cabWithICCManifest : KernelObligationCABZKManifest :=
  { cabManifest with iccBridgeAttestation := some bridgeManifest.bridge }

private def verifyWithICC : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK cabWithICCManifest (some baseManifest)

example : verifyWithICC.ok = true := by
  native_decide

example : verifyWithICC.iccBridgeAttestationPresent = true := by
  native_decide

example : verifyWithICC.iccBridgeAttestationConsistent = true := by
  native_decide

example : verifyWithICC.iccBridgeBoundaryConservative = true := by
  native_decide

-- ICC absent is NOT a failure (supplementary evidence)
private def verifyWithoutICC : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK cabManifest (some baseManifest)

example : verifyWithoutICC.ok = true := by
  native_decide

example : verifyWithoutICC.iccBridgeAttestationPresent = false := by
  native_decide

-- ICC with mismatched bindings fails consistency
private def otherBaseManifest : KernelObligationAssuranceManifest :=
  KernelObligationAssuranceManifest.ofBundle
    supportedObligationBundle "foundation" "rules" "kernel" .slice_checker_certified

private def cabMismatchedICC : KernelObligationCABZKManifest :=
  let otherCAB := KernelObligationCABZKManifest.ofBase otherBaseManifest
  { otherCAB with iccBridgeAttestation := some bridgeManifest.bridge }

private def verifyMismatchedICC : KernelObligationAssuranceVerifyReport :=
  KernelObligationAssuranceVerifyReport.ofCABZK cabMismatchedICC (some otherBaseManifest)

example : verifyMismatchedICC.ok = false := by
  native_decide

example : verifyMismatchedICC.iccBridgeAttestationConsistent = false := by
  native_decide

end HeytingLean.Tests.KernelAssurance.ICCBridge
