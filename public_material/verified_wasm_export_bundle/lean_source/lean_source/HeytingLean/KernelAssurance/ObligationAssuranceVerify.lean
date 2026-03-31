import HeytingLean.KernelAssurance.ObligationCABZKManifest

namespace HeytingLean.KernelAssurance

open Lean

structure KernelObligationAssuranceVerifyReport where
  mode : String
  ok : Bool
  baseBundleDigest : String
  baseGrantedTier : AssuranceTier
  baseTierDecisionConsistent : Bool
  baseClaimBoundaryConsistent : Bool
  externalBaseMatches : Bool
  checkerDigestMatches : Bool
  grantedTierMatchesBase : Bool
  loweringAttestationPresent : Bool
  loweringAttestationConsistent : Bool
  loweringBoundaryConservative : Bool
  checkerAttestationPresent : Bool
  checkerAttestationConsistent : Bool
  checkerBoundaryConservative : Bool
  iccBridgeAttestationPresent : Bool
  iccBridgeAttestationConsistent : Bool
  iccBridgeBoundaryConservative : Bool
  assuranceModeConsistent : Bool
  receiptBindingsMatch : Bool
  receiptConcreteIfPresent : Bool
  receiptBoundaryConservative : Bool
  failures : Array String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def containsText (haystack needle : String) : Bool :=
  decide ((haystack.splitOn needle).length > 1)

private def baseTierDecisionConsistentB (base : KernelObligationAssuranceManifest) : Bool :=
  decideObligationTier
      base.tierDecision.requested
      base.coverage
      base.replay
      base.checker == base.tierDecision

private def baseClaimBoundaryConsistentB (base : KernelObligationAssuranceManifest) : Bool :=
  base.claimBoundary = base.descriptor.claimBoundary

private def receiptBoundaryConservativeB (boundary : String) : Bool :=
  containsText boundary "proof verification remains external to this Lean manifest" &&
  containsText boundary "does not by itself prove Lean's full kernel"

private def checkerBoundaryConservativeB (boundary : String) : Bool :=
  containsText boundary "does not by itself prove Lean's full kernel"

private def loweringBoundaryConservativeB (boundary : String) : Bool :=
  containsText boundary "single kernel surface" &&
  containsText boundary "oracle-parametric" &&
  containsText boundary "fuel-bounded" &&
  containsText boundary "does not by itself prove Lean's full kernel"

private def iccBridgeBoundaryConservativeB (boundary : String) : Bool :=
  containsText boundary "Y-free" &&
  containsText boundary "does not by itself prove Lean's full kernel"

private def iccBridgeBindingsConsistentB
    (base : KernelObligationAssuranceManifest)
    (icc : ICCBridgeAttestation) : Bool :=
  icc.sourceBundleDigest == base.bundleDigest &&
  icc.sourceModule == base.descriptor.moduleName &&
  icc.sourceExportedObligations == base.coverage.exportedObligations &&
  icc.sourceDiscoveredObligations == base.coverage.discoveredObligations &&
  icc.yFreeLimitationAcknowledged

private def baseFailures (base : KernelObligationAssuranceManifest) : Array String :=
  Id.run do
    let mut failures : Array String := #[]
    if !baseTierDecisionConsistentB base then
      failures := failures.push "base tierDecision is inconsistent with recomputed obligation tier"
    if !baseClaimBoundaryConsistentB base then
      failures := failures.push "base claim boundary does not match descriptor claim boundary"
    return failures

def KernelObligationAssuranceVerifyReport.ofBase
    (base : KernelObligationAssuranceManifest) : KernelObligationAssuranceVerifyReport :=
  let failures := baseFailures base
  { mode := "base_only"
    ok := failures.isEmpty
    baseBundleDigest := base.bundleDigest
    baseGrantedTier := base.tierDecision.granted
    baseTierDecisionConsistent := baseTierDecisionConsistentB base
    baseClaimBoundaryConsistent := baseClaimBoundaryConsistentB base
    externalBaseMatches := true
    checkerDigestMatches := true
    grantedTierMatchesBase := true
    loweringAttestationPresent := false
    loweringAttestationConsistent := true
    loweringBoundaryConservative := true
    checkerAttestationPresent := false
    checkerAttestationConsistent := true
    checkerBoundaryConservative := true
    iccBridgeAttestationPresent := false
    iccBridgeAttestationConsistent := true
    iccBridgeBoundaryConservative := true
    assuranceModeConsistent := true
    receiptBindingsMatch := true
    receiptConcreteIfPresent := true
    receiptBoundaryConservative := true
    failures := failures }

def KernelObligationAssuranceVerifyReport.ofCABZK
    (cabZk : KernelObligationCABZKManifest)
    (externalBase? : Option KernelObligationAssuranceManifest := none) :
    KernelObligationAssuranceVerifyReport :=
  let base := cabZk.base
  let baseCheckerDigest := checkerDigestOfManifest base
  let externalBaseMatches :=
    match externalBase? with
    | some externalBase => externalBase == base
    | none => true
  let checkerDigestMatches := cabZk.checkerDigest = baseCheckerDigest
  let grantedTierMatchesBase := cabZk.grantedTier = base.tierDecision.granted
  let loweringAttestationPresent := cabZk.loweringAttestation.isSome
  let loweringAttestationConsistent :=
    match cabZk.loweringAttestation with
    | some attestation => attestation == LoweringAttestation.ofBase base
    | none => true
  let loweringBoundaryConservative :=
    match cabZk.loweringAttestation with
    | some attestation => loweringBoundaryConservativeB attestation.claimBoundary
    | none => true
  let checkerAttestationPresent := cabZk.checkerAttestation.isSome
  let checkerAttestationConsistent :=
    match cabZk.checkerAttestation with
    | some attestation => attestation == CheckerAttestation.ofBase base
    | none => true
  let checkerBoundaryConservative :=
    match cabZk.checkerAttestation with
    | some attestation => checkerBoundaryConservativeB attestation.claimBoundary
    | none => true
  let iccBridgeAttestationPresent := cabZk.iccBridgeAttestation.isSome
  let iccBridgeAttestationConsistent :=
    match cabZk.iccBridgeAttestation with
    | some icc => iccBridgeBindingsConsistentB base icc
    | none => true
  let iccBridgeBoundaryConservative :=
    match cabZk.iccBridgeAttestation with
    | some icc => iccBridgeBoundaryConservativeB icc.claimBoundary
    | none => true
  let assuranceModeConsistent :=
    match cabZk.assuranceMode, cabZk.zkReceipt with
    | .cab_only, none => true
    | .cab_only, some _ => false
    | .cab_plus_zk_receipt, some receipt => receipt.isConcrete
    | .cab_plus_zk_receipt, none => false
  let receiptBindingsMatch :=
    match cabZk.zkReceipt with
    | some receipt =>
        receipt.checkerDigest = baseCheckerDigest &&
        receipt.bundleDigest = base.bundleDigest &&
        cabZk.receiptClaimBoundary = receipt.claimBoundary
    | none =>
        cabZk.assuranceMode = .cab_only
  let receiptConcreteIfPresent :=
    match cabZk.zkReceipt with
    | some receipt => receipt.isConcrete
    | none => true
  let receiptBoundaryConservative :=
    match cabZk.zkReceipt with
    | some _ => receiptBoundaryConservativeB cabZk.receiptClaimBoundary
    | none => containsText cabZk.receiptClaimBoundary "No concrete ZK receipt metadata attached"
  let failures := Id.run do
    let mut failures := baseFailures base
    if !externalBaseMatches then
      failures := failures.push "external base manifest does not match the CAB-ZK embedded base manifest"
    if !checkerDigestMatches then
      failures := failures.push "CAB-ZK checkerDigest does not match the embedded base checker digest"
    if !grantedTierMatchesBase then
      failures := failures.push "CAB-ZK grantedTier does not match the embedded base granted tier"
    if !loweringAttestationPresent then
      failures := failures.push "CAB-ZK lowering attestation is missing"
    if !loweringAttestationConsistent then
      failures := failures.push "CAB-ZK lowering attestation does not match the embedded base manifest"
    if !loweringBoundaryConservative then
      failures := failures.push "CAB-ZK lowering claim boundary is not conservative enough"
    if !checkerAttestationPresent then
      failures := failures.push "CAB-ZK checker attestation is missing"
    if !checkerAttestationConsistent then
      failures := failures.push "CAB-ZK checker attestation does not match the embedded base manifest"
    if !checkerBoundaryConservative then
      failures := failures.push "CAB-ZK checker claim boundary is not conservative enough"
    if !iccBridgeAttestationConsistent then
      failures := failures.push "CAB-ZK ICC bridge attestation bindings do not match the embedded base manifest"
    if !iccBridgeBoundaryConservative then
      failures := failures.push "CAB-ZK ICC bridge claim boundary is not conservative enough"
    if !assuranceModeConsistent then
      failures := failures.push "CAB-ZK assuranceMode is inconsistent with the attached receipt"
    if !receiptBindingsMatch then
      failures := failures.push "CAB-ZK receipt bindings do not match the embedded base manifest"
    if !receiptConcreteIfPresent then
      failures := failures.push "CAB-ZK receipt is present but not concrete"
    if !receiptBoundaryConservative then
      failures := failures.push "CAB-ZK receipt claim boundary is not conservative enough"
    return failures
  { mode := "cab_zk"
    ok := failures.isEmpty
    baseBundleDigest := base.bundleDigest
    baseGrantedTier := base.tierDecision.granted
    baseTierDecisionConsistent := baseTierDecisionConsistentB base
    baseClaimBoundaryConsistent := baseClaimBoundaryConsistentB base
    externalBaseMatches := externalBaseMatches
    checkerDigestMatches := checkerDigestMatches
    grantedTierMatchesBase := grantedTierMatchesBase
    loweringAttestationPresent := loweringAttestationPresent
    loweringAttestationConsistent := loweringAttestationConsistent
    loweringBoundaryConservative := loweringBoundaryConservative
    checkerAttestationPresent := checkerAttestationPresent
    checkerAttestationConsistent := checkerAttestationConsistent
    checkerBoundaryConservative := checkerBoundaryConservative
    iccBridgeAttestationPresent := iccBridgeAttestationPresent
    iccBridgeAttestationConsistent := iccBridgeAttestationConsistent
    iccBridgeBoundaryConservative := iccBridgeBoundaryConservative
    assuranceModeConsistent := assuranceModeConsistent
    receiptBindingsMatch := receiptBindingsMatch
    receiptConcreteIfPresent := receiptConcreteIfPresent
    receiptBoundaryConservative := receiptBoundaryConservative
    failures := failures }

end HeytingLean.KernelAssurance
