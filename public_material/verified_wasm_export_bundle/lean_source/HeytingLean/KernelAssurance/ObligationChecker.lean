import HeytingLean.KernelAssurance.ObligationReplay
import HeytingLean.LoF.LeanKernel.VerifierObligationJson

namespace HeytingLean.KernelAssurance

open Lean

structure ObligationCheckerFailure where
  id : String
  declName : String
  reason : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

structure ObligationCheckerReport where
  checked : Nat
  passed : Nat
  failed : Nat
  bundleDigestValid : Bool
  tamperFailures : Nat
  classificationFailures : Nat
  dependencyFailures : Nat
  countFailures : Nat
  failures : Array ObligationCheckerFailure
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def checkerFailureOf (entry : ObligationEntry) (reason : String) : ObligationCheckerFailure :=
  { id := entry.id, declName := entry.declName, reason := reason }

private def containsText (haystack needle : String) : Bool :=
  decide ((haystack.splitOn needle).length > 1)

private def depsMatch
    (lhs rhs : Array HeytingLean.LoF.LeanKernel.DependencyRef) : Bool :=
  if lhs.size = rhs.size then
    Id.run do
      for i in [0:lhs.size] do
        match lhs[i]?, rhs[i]? with
        | some a, some b =>
            if !(HeytingLean.LoF.LeanKernel.DependencyRef.id a =
                  HeytingLean.LoF.LeanKernel.DependencyRef.id b &&
                HeytingLean.LoF.LeanKernel.DependencyRef.edgeKind a =
                  HeytingLean.LoF.LeanKernel.DependencyRef.edgeKind b) then
              return false
        | _, _ =>
            return false
      return true
  else
    false

private def checkEntry (entry : ObligationEntry) : Array ObligationCheckerFailure :=
  let expectedFamily := familyOfObligation entry.obligation
  let expectedStatus := statusOfObligation entry.obligation
  let expectedMachineDigest := obligationJsonDigest entry.obligation.machineJson
  let expectedFinalDigest := obligationJsonDigest entry.obligation.finalJson
  let expectedEntryDigest :=
    mkObligationEntryDigest
      entry.obligation.id entry.obligation.declName entry.obligation.declKind entry.obligation.traceRole
      entry.obligation.traceGrain entry.obligation.verificationMode entry.obligation.joinGroup
      entry.obligation.replayKind entry.obligation.deps expectedFamily expectedStatus
      entry.obligation.projectedBetaZetaSteps entry.obligation.stepCount entry.obligation.deltaIotaSteps
      entry.obligation.nodeCount entry.obligation.inputExprRepr entry.obligation.outputExprRepr
      entry.obligation.nativeWhnfRepr entry.obligation.expectedTagTerm expectedMachineDigest expectedFinalDigest
  let failures0 : Array ObligationCheckerFailure := #[]
  let failures1 :=
    if entry.machineDigest = expectedMachineDigest && entry.finalDigest = expectedFinalDigest then
      failures0
    else
      failures0.push (checkerFailureOf entry "payload digest mismatch")
  let failures2 :=
    if entry.entryDigest = expectedEntryDigest then
      failures1
    else
      failures1.push (checkerFailureOf entry "entry digest mismatch")
  let failures3 :=
    if entry.family = expectedFamily && entry.status = expectedStatus then
      failures2
    else
      failures2.push (checkerFailureOf entry "family or status classification mismatch")
  let failures4 :=
    if entry.id = entry.obligation.id &&
        entry.declName = entry.obligation.declName &&
        entry.declKind = entry.obligation.declKind &&
        entry.traceRole = entry.obligation.traceRole &&
        entry.traceGrain = entry.obligation.traceGrain &&
        entry.verificationMode = entry.obligation.verificationMode &&
        entry.replayKind = entry.obligation.replayKind &&
        entry.joinGroup = entry.obligation.joinGroup then
      failures3
    else
      failures3.push (checkerFailureOf entry "entry metadata mismatch")
  let failures5 :=
    if depsMatch entry.deps entry.obligation.deps then
      failures4
    else
      failures4.push (checkerFailureOf entry "dependency metadata mismatch")
  failures5

private def duplicateIdFailures (bundle : ObligationSliceBundle) : Array ObligationCheckerFailure :=
  Id.run do
    let mut seen : Array String := #[]
    let mut failures : Array ObligationCheckerFailure := #[]
    for entry in bundle.entries do
      if seen.contains entry.id then
        failures := failures.push (checkerFailureOf entry "duplicate obligation id")
      else
        seen := seen.push entry.id
    failures

private def countFailuresOfBundle (bundle : ObligationSliceBundle) : Array ObligationCheckerFailure :=
  Id.run do
    let coverage := ObligationCoverageReport.ofBundle bundle
    let totalOk :=
      coverage.obligationsTotal =
        coverage.supportedObligations + coverage.blockedObligations + coverage.unclassifiedObligations
    let selectedOk := bundle.selectedDeclarations <= bundle.totalDeclarations
    let obligationsOk := bundle.obligationsTotal = bundle.entries.size
    let eligibleOk := bundle.eligibleTraceEntries >= bundle.obligationsTotal
    let rootEntry := bundle.entries.getD 0 default
    let mut failures : Array ObligationCheckerFailure := #[]
    if !totalOk then
      failures := failures.push (checkerFailureOf rootEntry "coverage counts do not partition obligation totals")
    if !selectedOk then
      failures := failures.push (checkerFailureOf rootEntry "selected declarations exceed total declarations")
    if !obligationsOk then
      failures := failures.push (checkerFailureOf rootEntry "bundle obligation count does not match entries")
    if !eligibleOk then
      failures := failures.push (checkerFailureOf rootEntry "eligible trace entry count is smaller than exported obligations")
    failures

private def isTamperFailure (failure : ObligationCheckerFailure) : Bool :=
  containsText failure.reason "digest" || containsText failure.reason "metadata"

private def isClassificationFailure (failure : ObligationCheckerFailure) : Bool :=
  containsText failure.reason "classification"

private def isDependencyFailure (failure : ObligationCheckerFailure) : Bool :=
  containsText failure.reason "dependency" || containsText failure.reason "duplicate"

private def isCountFailure (failure : ObligationCheckerFailure) : Bool :=
  containsText failure.reason "count" || containsText failure.reason "total" || containsText failure.reason "selected" || containsText failure.reason "eligible"

def ObligationCheckerReport.ofBundle (bundle : ObligationSliceBundle) : ObligationCheckerReport :=
  Id.run do
    let mut failures : Array ObligationCheckerFailure := #[]
    for entry in bundle.entries do
      failures := failures ++ checkEntry entry
    failures := failures ++ duplicateIdFailures bundle
    failures := failures ++ countFailuresOfBundle bundle
    let tamperFailures := failures.foldl (fun acc failure => if isTamperFailure failure then acc + 1 else acc) 0
    let classificationFailures := failures.foldl (fun acc failure => if isClassificationFailure failure then acc + 1 else acc) 0
    let dependencyFailures := failures.foldl (fun acc failure => if isDependencyFailure failure then acc + 1 else acc) 0
    let countFailures := failures.foldl (fun acc failure => if isCountFailure failure then acc + 1 else acc) 0
    {
      checked := bundle.entries.size
      passed := bundle.entries.size - failures.size
      failed := failures.size
      bundleDigestValid := bundle.bundleDigestValid
      tamperFailures := tamperFailures
      classificationFailures := classificationFailures
      dependencyFailures := dependencyFailures
      countFailures := countFailures
      failures := failures
    }

end HeytingLean.KernelAssurance
