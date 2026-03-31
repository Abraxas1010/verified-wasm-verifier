import HeytingLean.KernelAssurance.CheckerAttestation
import HeytingLean.KernelAssurance.ExportSupport
import HeytingLean.KernelAssurance.ICCBridgeAttestation
import HeytingLean.KernelAssurance.LoweringAttestation
import HeytingLean.KernelAssurance.ObligationManifest
import HeytingLean.KernelAssurance.ZKReceipt

namespace HeytingLean.KernelAssurance

open Lean

structure KernelObligationCABZKManifest where
  version : String := "kernel-obligation-cab-zk-v1"
  assuranceMode : AssuranceMode := .cab_only
  base : KernelObligationAssuranceManifest
  grantedTier : AssuranceTier
  checkerDigest : String
  cabClaimBoundary : String
  loweringAttestation : Option LoweringAttestation := none
  checkerAttestation : Option CheckerAttestation := none
  iccBridgeAttestation : Option ICCBridgeAttestation := none
  zkReceipt : Option ZKReceiptMetadata := none
  receiptClaimBoundary : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def checkerDigestOfManifest (manifest : KernelObligationAssuranceManifest) : String :=
  structuralDigest manifest.checker

def normalizeZKReceipt
    (base : KernelObligationAssuranceManifest)
    (receipt : ZKReceiptMetadata) : ZKReceiptMetadata :=
  let checkerDigest := checkerDigestOfManifest base
  let bundleDigest := base.bundleDigest
  let proofSystem :=
    if receipt.proofSystem.isEmpty then "unknown_zk" else receipt.proofSystem
  let executionClaim :=
    if receipt.executionClaim.isEmpty then
      "Proves checker execution over the declared obligation bundle."
    else
      receipt.executionClaim
  { receipt with
      proofSystem := proofSystem
      checkerDigest := checkerDigest
      bundleDigest := bundleDigest
      executionClaim := executionClaim
      claimBoundary := mkZKReceiptClaimBoundary proofSystem checkerDigest bundleDigest }

def normalizeConcreteZKReceipt?
    (base : KernelObligationAssuranceManifest)
    (receipt : ZKReceiptMetadata) : Option ZKReceiptMetadata :=
  let normalized := normalizeZKReceipt base receipt
  if normalized.isConcrete then
    some normalized
  else
    none

def KernelObligationCABZKManifest.ofBase
    (base : KernelObligationAssuranceManifest)
    (zkReceipt? : Option ZKReceiptMetadata := none) : KernelObligationCABZKManifest :=
  let checkerDigest := checkerDigestOfManifest base
  let loweringAttestation := some <| LoweringAttestation.ofBase base
  let checkerAttestation := some <| CheckerAttestation.ofBase base
  let normalizedReceipt? := zkReceipt?.bind (normalizeConcreteZKReceipt? base)
  let assuranceMode :=
    match normalizedReceipt? with
    | some _ => .cab_plus_zk_receipt
    | none => .cab_only
  let receiptClaimBoundary :=
    match normalizedReceipt? with
    | some receipt => receipt.claimBoundary
    | none => "No concrete ZK receipt metadata attached; CAB claim boundary only."
  { assuranceMode := assuranceMode
    base := base
    grantedTier := base.tierDecision.granted
    checkerDigest := checkerDigest
    cabClaimBoundary := base.claimBoundary
    loweringAttestation := loweringAttestation
    checkerAttestation := checkerAttestation
    zkReceipt := normalizedReceipt?
    receiptClaimBoundary := receiptClaimBoundary }

end HeytingLean.KernelAssurance
