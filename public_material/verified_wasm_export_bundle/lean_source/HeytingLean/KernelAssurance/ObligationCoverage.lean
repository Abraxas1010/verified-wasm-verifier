import HeytingLean.KernelAssurance.ObligationBundle

namespace HeytingLean.KernelAssurance

open Lean

structure ObligationFamilyLedger where
  family : ObligationFamilyId
  discovered : Nat
  exported : Nat
  replaySupported : Nat
  checkerSupported : Nat
  blocked : Nat
  unclassified : Nat
  deriving Repr, Inhabited, BEq, ToJson, FromJson

structure ObligationCoverageReport where
  version : String := "kernel-obligation-assurance-v1"
  moduleName : String
  traceGrain : String
  loweringFormallyVerified : Bool := true
  families : Array ObligationFamilyLedger
  discoveredFamilyCount : Nat
  exportedFamilyCount : Nat
  replaySupportedFamilyCount : Nat
  checkerSupportedFamilyCount : Nat
  blockedFamilyCount : Nat
  unclassifiedFamilyCount : Nat
  selectedDeclarations : Nat
  totalDeclarations : Nat
  discoveredObligations : Nat
  exportedObligations : Nat
  eligibleTraceEntries : Nat
  obligationsTotal : Nat
  supportedObligations : Nat
  blockedObligations : Nat
  unclassifiedObligations : Nat
  bundleDigest : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def obligationFamilyLedgerOf
    (entries : Array ObligationEntry)
    (family : ObligationFamilyId) : Option ObligationFamilyLedger :=
  let familyEntries := entries.filter (fun e => e.family = family)
  if familyEntries.isEmpty then
    none
  else
    let supportedObligations := familyEntries.foldl (fun acc e => if e.status = .supported then acc + 1 else acc) 0
    let blockedObligations := familyEntries.foldl (fun acc e => if e.status = .blocked then acc + 1 else acc) 0
    let unclassifiedObligations := familyEntries.foldl (fun acc e => if e.status = .unclassified then acc + 1 else acc) 0
    some {
      family := family
      discovered := familyEntries.size
      exported := familyEntries.size
      replaySupported := supportedObligations
      checkerSupported := supportedObligations
      blocked := blockedObligations
      unclassified := unclassifiedObligations
    }

private def jsonNatD (json : Json) (field : String) : Nat :=
  match json.getObjValAs? Nat field with
  | .ok value => value
  | .error _ => 0

private def jsonBoolD (json : Json) (field : String) : Bool :=
  match json.getObjValAs? Bool field with
  | .ok value => value
  | .error _ => false

private def payloadOperationExported (operation : Json) : Bool :=
  jsonBoolD operation "eligible" && !jsonBoolD operation "semantic_check_skipped"

private structure SourceCoverageSummary where
  selectedDeclarations : Nat := 0
  totalDeclarations : Nat := 0
  discoveredObligations : Nat := 0
  exportedObligations : Nat := 0
  families : Array ObligationFamilyLedger := #[]

private def sourceFamilyLedgerOfPayload
    (payload : Json)
    (family : ObligationFamilyId) : Option ObligationFamilyLedger :=
  let declarations :=
    match payload.getObjVal? "declarations" with
    | .ok (.arr xs) => xs
    | _ => #[]
  let counts :=
    declarations.foldl
      (init := (0, 0, 0, 0))
      fun (discovered, exported, blocked, unclassified) decl =>
        let traceCounts :=
          match decl.getObjVal? "trace_entries" with
          | .ok (.arr entries) =>
              entries.foldl
                (init := (0, 0, 0, 0))
                fun (dAcc, eAcc, bAcc, uAcc) entry =>
                  if family = .whnf then
                    let exported' := jsonBoolD entry "gpu_verifiable" && jsonBoolD entry "eligible"
                    let dAcc := dAcc + 1
                    let eAcc := if exported' then eAcc + 1 else eAcc
                    let bAcc := if exported' then bAcc else bAcc + 1
                    (dAcc, eAcc, bAcc, uAcc)
                  else
                    (dAcc, eAcc, bAcc, uAcc)
          | _ => (0, 0, 0, 0)
        let opCounts :=
          match decl.getObjVal? "operations" with
          | .ok (.arr operations) =>
              operations.foldl
                (init := (0, 0, 0, 0))
                fun (dAcc, eAcc, bAcc, uAcc) operation =>
                  let opFamily := familyOfVerificationMode <| match operation.getObjValAs? String "op_type" with
                    | .ok value => value
                    | .error _ => ""
                  if opFamily = family then
                    let exported' := payloadOperationExported operation
                    let dAcc := dAcc + 1
                    let eAcc := if exported' then eAcc + 1 else eAcc
                    let bAcc := if exported' || family = .unknown then bAcc else bAcc + 1
                    let uAcc := if exported' || family ≠ .unknown then uAcc else uAcc + 1
                    (dAcc, eAcc, bAcc, uAcc)
                  else
                    (dAcc, eAcc, bAcc, uAcc)
          | _ => (0, 0, 0, 0)
        let (td, te, tb, tu) := traceCounts
        let (od, oe, ob, ou) := opCounts
        (discovered + td + od, exported + te + oe, blocked + tb + ob, unclassified + tu + ou)
  let (discovered, exported, blocked, unclassified) := counts
  if discovered = 0 then
    none
  else
    some {
      family := family
      discovered := discovered
      exported := exported
      replaySupported := 0
      checkerSupported := 0
      blocked := blocked
      unclassified := unclassified
    }

private def sourceCoverageSummaryOfPayload (payload : Json) : SourceCoverageSummary :=
  let families := allObligationFamilies.filterMap (sourceFamilyLedgerOfPayload payload)
  {
    selectedDeclarations := jsonNatD payload "selected_declarations"
    totalDeclarations := jsonNatD payload "total_declarations"
    discoveredObligations := families.foldl (fun acc row => acc + row.discovered) 0
    exportedObligations := families.foldl (fun acc row => acc + row.exported) 0
    families := families
  }

private def mergedFamilyLedger
    (base : Array ObligationFamilyLedger)
    (source : Array ObligationFamilyLedger)
    (family : ObligationFamilyId) : Option ObligationFamilyLedger :=
  let base? := base.find? (fun row => row.family = family)
  let source? := source.find? (fun row => row.family = family)
  match base?, source? with
  | none, none => none
  | _, _ =>
      let base := base?.getD { (default : ObligationFamilyLedger) with family := family }
      let source := source?.getD { (default : ObligationFamilyLedger) with family := family }
      let discovered := Nat.max base.discovered source.discovered
      let exported := Nat.max base.exported source.exported
      let missingEligible := exported - base.exported
      let blocked :=
        base.blocked + source.blocked + if family = .unknown then 0 else missingEligible
      let unclassified :=
        base.unclassified + source.unclassified + if family = .unknown then missingEligible else 0
      some {
        family := family
        discovered := discovered
        exported := exported
        replaySupported := base.replaySupported
        checkerSupported := base.checkerSupported
        blocked := blocked
        unclassified := unclassified
      }

def ObligationCoverageReport.ofBundleWithSourcePayload
    (bundle : ObligationSliceBundle)
    (sourcePayload? : Option Json := none) : ObligationCoverageReport :=
  let baseFamilies := allObligationFamilies.filterMap (obligationFamilyLedgerOf bundle.entries)
  let sourceSummary := sourcePayload?.map sourceCoverageSummaryOfPayload
  let families :=
    match sourceSummary with
    | some summary =>
        allObligationFamilies.filterMap (mergedFamilyLedger baseFamilies summary.families)
    | none =>
        baseFamilies
  let discoveredFamilyCount := families.size
  let exportedFamilyCount :=
    families.foldl (fun acc row => if row.exported > 0 then acc + 1 else acc) 0
  let replaySupportedFamilyCount :=
    families.foldl (fun acc row => if row.replaySupported > 0 then acc + 1 else acc) 0
  let checkerSupportedFamilyCount :=
    families.foldl (fun acc row => if row.checkerSupported > 0 then acc + 1 else acc) 0
  let blockedFamilyCount :=
    families.foldl (fun acc row => if row.blocked > 0 then acc + 1 else acc) 0
  let unclassifiedFamilyCount :=
    families.foldl (fun acc row => if row.unclassified > 0 then acc + 1 else acc) 0
  let discoveredObligations := (sourceSummary.map (·.discoveredObligations)).getD bundle.entries.size
  let exportedObligations := (sourceSummary.map (·.exportedObligations)).getD bundle.entries.size
  let blockedObligations := families.foldl (fun acc row => acc + row.blocked) 0
  let unclassifiedObligations := families.foldl (fun acc row => acc + row.unclassified) 0
  {
    moduleName := bundle.descriptor.moduleName
    traceGrain := bundle.descriptor.traceGrain
    loweringFormallyVerified := true
    families := families
    discoveredFamilyCount := discoveredFamilyCount
    exportedFamilyCount := exportedFamilyCount
    replaySupportedFamilyCount := replaySupportedFamilyCount
    checkerSupportedFamilyCount := checkerSupportedFamilyCount
    blockedFamilyCount := blockedFamilyCount
    unclassifiedFamilyCount := unclassifiedFamilyCount
    selectedDeclarations := (sourceSummary.map (·.selectedDeclarations)).getD bundle.selectedDeclarations
    totalDeclarations := (sourceSummary.map (·.totalDeclarations)).getD bundle.totalDeclarations
    discoveredObligations := discoveredObligations
    exportedObligations := exportedObligations
    eligibleTraceEntries := Nat.max bundle.eligibleTraceEntries exportedObligations
    obligationsTotal := bundle.obligationsTotal
    supportedObligations := bundle.exportedSupported
    blockedObligations := blockedObligations
    unclassifiedObligations := unclassifiedObligations
    bundleDigest := bundle.bundleDigest
  }

def ObligationCoverageReport.ofBundle (bundle : ObligationSliceBundle) : ObligationCoverageReport :=
  ofBundleWithSourcePayload bundle none

end HeytingLean.KernelAssurance
