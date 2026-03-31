import HeytingLean.Tests.KernelAssurance.ObligationFixture
import HeytingLean.KernelAssurance.ObligationCABZKManifest

namespace HeytingLean.Tests.KernelAssurance.CABZK

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
    executionClaim := "Proves acceptance of the supported obligation slice."
    claimBoundary := "" }

private def cabOnlyManifest : KernelObligationCABZKManifest :=
  KernelObligationCABZKManifest.ofBase baseManifest

private def receiptManifest : KernelObligationCABZKManifest :=
  KernelObligationCABZKManifest.ofBase baseManifest (some receiptInput)

private def incompleteReceiptInput : ZKReceiptMetadata :=
  { proofSystem := "groth16"
    circuitKind := "checker_acceptance"
    checkerDigest := ""
    bundleDigest := ""
    receiptDigest := ""
    publicInputDigest := ""
    verifierDigest := ""
    executionClaim := ""
    claimBoundary := "" }

private def incompleteReceiptManifest : KernelObligationCABZKManifest :=
  KernelObligationCABZKManifest.ofBase baseManifest (some incompleteReceiptInput)

example : cabOnlyManifest.assuranceMode = .cab_only := rfl

example : cabOnlyManifest.grantedTier = baseManifest.tierDecision.granted := by
  native_decide

example : receiptManifest.assuranceMode = .cab_plus_zk_receipt := rfl

example : receiptManifest.grantedTier = baseManifest.tierDecision.granted := by
  native_decide

example : receiptManifest.checkerDigest = checkerDigestOfManifest baseManifest := by
  native_decide

example : receiptManifest.zkReceipt.isSome = true := by
  native_decide

example : (receiptManifest.zkReceipt.getD default).isConcrete = true := by
  native_decide

example : (receiptManifest.zkReceipt.getD default).bundleDigest = baseManifest.bundleDigest := by
  native_decide

example : (receiptManifest.zkReceipt.getD default).checkerDigest = checkerDigestOfManifest baseManifest := by
  native_decide

example :
    decide ((receiptManifest.receiptClaimBoundary.splitOn
      "proof verification remains external to this Lean manifest").length > 1) := by
  native_decide

example : incompleteReceiptManifest.assuranceMode = .cab_only := rfl

example : incompleteReceiptManifest.zkReceipt.isNone = true := by
  native_decide

example :
    decide ((incompleteReceiptManifest.receiptClaimBoundary.splitOn
      "No concrete ZK receipt metadata attached").length > 1) := by
  native_decide

end HeytingLean.Tests.KernelAssurance.CABZK
