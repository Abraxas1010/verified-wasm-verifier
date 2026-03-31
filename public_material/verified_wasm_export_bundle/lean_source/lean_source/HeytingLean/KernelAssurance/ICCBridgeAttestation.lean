import Lean.Data.Json
import HeytingLean.KernelAssurance.ExportSupport
import HeytingLean.KernelAssurance.ObligationManifest

namespace HeytingLean.KernelAssurance

open Lean

structure ICCBridgeAttestation where
  version : String := "kernel-obligation-icc-bridge-attestation-v1"
  sourceBundleDigest : String
  sourceModule : String
  sourceExportedObligations : Nat
  sourceDiscoveredObligations : Nat
  iccCarrierDigest : String
  iccModuleRoots : Array String
  iccDeclsTotal : Nat
  iccDeclsSupported : Nat
  noLossDeclsSeen : Nat
  noLossDeclsChecked : Nat
  noLossFailures : Nat
  noLossStatus : Bool
  moduleAlignment : Bool
  declAlignment : Bool
  attested : Bool
  yFreeLimitationAcknowledged : Bool := true
  claimBoundary : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

structure KernelObligationICCBridgeManifest where
  version : String := "kernel-obligation-icc-bridge-v1"
  base : KernelObligationAssuranceManifest
  grantedTier : AssuranceTier
  bridge : ICCBridgeAttestation
  claimBoundary : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def jsonNatD (json : Json) (field : String) (fallback : Nat := 0) : Nat :=
  match json.getObjValAs? Nat field with
  | .ok value => value
  | .error _ => fallback

private def jsonBoolD (json : Json) (field : String) (fallback : Bool := false) : Bool :=
  match json.getObjValAs? Bool field with
  | .ok value => value
  | .error _ => fallback

private def jsonStringD (json : Json) (field : String) (fallback : String := "") : String :=
  match json.getObjValAs? String field with
  | .ok value => value
  | .error _ => fallback

private def jsonStringArrayD (json : Json) (field : String) : Array String :=
  match json.getObjVal? field with
  | .ok value =>
      match value.getArr? with
      | .ok values =>
          values.filterMap fun item =>
            match item.getStr? with
            | .ok text => some text
            | .error _ => none
      | .error _ => #[]
  | .error _ => #[]

private def jsonNestedNatD (json : Json) (outer inner : String) (fallback : Nat := 0) : Nat :=
  match json.getObjVal? outer with
  | .ok nested => jsonNatD nested inner fallback
  | .error _ => fallback

private def pushUnique (acc : Array String) (value : String) : Array String :=
  if acc.any (· == value) then acc else acc.push value

private def mergeUnique (lhs rhs : Array String) : Array String :=
  rhs.foldl pushUnique lhs

private def sourceModuleOf (base : KernelObligationAssuranceManifest) (sourcePayload? : Option Json) : String :=
  match sourcePayload? with
  | some payload => jsonStringD payload "module" base.descriptor.moduleName
  | none => base.descriptor.moduleName

def mkICCBridgeClaimBoundary (moduleAlignment declAlignment noLossStatus : Bool) : String :=
  let summary :=
    if moduleAlignment && declAlignment && noLossStatus then
      "ICC/ICCKernel bridge attestation confirmed module-root alignment and no-loss export/recheck parity over the declared slice."
    else
      "ICC/ICCKernel bridge attestation recorded a mismatch or failed no-loss recheck over the declared slice."
  summary ++
    " This is transport evidence only, covering the closed Y-free fragment of ICC." ++
    " It does not promote ICC/ICCKernel to the trusted checker and does not by itself prove Lean's full kernel."

def ICCBridgeAttestation.ofInputs
    (base : KernelObligationAssuranceManifest)
    (sourcePayload? : Option Json := none)
    (iccExportJson iccNoLossJson : Json) : ICCBridgeAttestation :=
  let sourceModule := sourceModuleOf base sourcePayload?
  let exportRoots := jsonStringArrayD iccExportJson "moduleRoots"
  let noLossRoots := jsonStringArrayD iccNoLossJson "moduleRoots"
  let moduleAlignment :=
    (exportRoots.isEmpty || exportRoots.any (· == sourceModule)) &&
      (noLossRoots.isEmpty || noLossRoots.any (· == sourceModule))
  let iccDeclsTotal := jsonNestedNatD iccExportJson "summary" "declsTotal"
  let iccDeclsSupported := jsonNestedNatD iccExportJson "summary" "declsSupported"
  let noLossDeclsSeen := jsonNatD iccNoLossJson "declsSeen"
  let noLossDeclsChecked := jsonNatD iccNoLossJson "declsChecked"
  let noLossFailures := jsonNatD iccNoLossJson "failuresCount"
  let noLossStatus := jsonBoolD iccNoLossJson "ok"
  let declAlignment := iccDeclsSupported == noLossDeclsChecked && iccDeclsTotal == noLossDeclsSeen
  let attested := moduleAlignment && declAlignment && noLossStatus && noLossFailures == 0
  let iccCarrierDigest :=
    structuralDigest <| Json.mkObj
      [("icc_export", iccExportJson), ("icc_no_loss", iccNoLossJson)]
  let claimBoundary := mkICCBridgeClaimBoundary moduleAlignment declAlignment noLossStatus
  { sourceBundleDigest := base.bundleDigest
    sourceModule := sourceModule
    sourceExportedObligations := base.coverage.exportedObligations
    sourceDiscoveredObligations := base.coverage.discoveredObligations
    iccCarrierDigest := iccCarrierDigest
    iccModuleRoots := mergeUnique exportRoots noLossRoots
    iccDeclsTotal := iccDeclsTotal
    iccDeclsSupported := iccDeclsSupported
    noLossDeclsSeen := noLossDeclsSeen
    noLossDeclsChecked := noLossDeclsChecked
    noLossFailures := noLossFailures
    noLossStatus := noLossStatus
    moduleAlignment := moduleAlignment
    declAlignment := declAlignment
    attested := attested
    claimBoundary := claimBoundary }

def KernelObligationICCBridgeManifest.ofBase
    (base : KernelObligationAssuranceManifest)
    (iccExportJson iccNoLossJson : Json)
    (sourcePayload? : Option Json := none) : KernelObligationICCBridgeManifest :=
  let bridge := ICCBridgeAttestation.ofInputs base sourcePayload? iccExportJson iccNoLossJson
  { base := base
    grantedTier := base.tierDecision.granted
    bridge := bridge
    claimBoundary := bridge.claimBoundary }

end HeytingLean.KernelAssurance
