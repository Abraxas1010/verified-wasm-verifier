import HeytingLean.KernelAssurance.ObligationCoverage

namespace HeytingLean.KernelAssurance

open Lean
open HeytingLean.LoF.LeanKernel

structure ObligationReplayFailure where
  id : String
  declName : String
  reason : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

structure ObligationReplayReport where
  checked : Nat
  passed : Nat
  failed : Nat
  skippedBlocked : Nat
  skippedUnclassified : Nat
  bundleDigestValid : Bool
  dependencyFailures : Nat
  payloadFailures : Nat
  failures : Array ObligationReplayFailure
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def obligationReplayFailureOf (entry : ObligationEntry) (reason : String) : ObligationReplayFailure :=
  { id := entry.id, declName := entry.declName, reason := reason }

private def containsText (haystack needle : String) : Bool :=
  decide ((haystack.splitOn needle).length > 1)

private def isNullJson (json : Json) : Bool :=
  json == Json.null

private def payloadFailureReason? (entry : ObligationEntry) : Option String :=
  if entry.id.isEmpty then
    some "obligation id is empty"
  else if entry.joinGroup.isEmpty then
    some "join group is empty"
  else
    match expectedReplayKind? entry.verificationMode with
    | none => some "verification mode is not in the fenced obligation slice"
    | some .whnfCall =>
        if entry.replayKind ≠ .whnfCall then
          some "whnf_call obligation has the wrong replay kind"
        else if entry.traceGrain ≠ "whnf" then
          some "whnf_call obligation is not tagged as whnf grain"
        else if isNullJson entry.obligation.machineJson then
          some "whnf_call obligation is missing machine_json"
        else if isNullJson entry.obligation.finalJson then
          some "whnf_call obligation is missing final_json"
        else if entry.inputExprRepr.isEmpty || entry.outputExprRepr.isEmpty then
          some "whnf_call obligation is missing input/output repr"
        else
          none
    | some .tagCheck =>
        if entry.replayKind ≠ .tagCheck then
          some "tag-check obligation has the wrong replay kind"
        else if entry.verificationMode = "whnf_call" then
          some "whnf_call cannot replay as a tag check"
        else if isNullJson entry.obligation.machineJson then
          some "tag-check obligation is missing machine_json"
        else if entry.outputExprRepr.isEmpty then
          some "tag-check obligation is missing output repr"
        else
          none
    | some .whnfStep =>
        some "whnf_step obligations are outside the current replay lane"

private def depsClosed (entry : ObligationEntry) (presentIds : Array String) : Bool :=
  entry.deps.all fun dep => presentIds.contains dep.id

private def replaySupportedEntry
    (entry : ObligationEntry)
    (presentIds : Array String) : Option ObligationReplayFailure :=
  if entry.machineDigest ≠ obligationJsonDigest entry.obligation.machineJson then
    some (obligationReplayFailureOf entry "machine digest mismatch")
  else if entry.finalDigest ≠ obligationJsonDigest entry.obligation.finalJson then
    some (obligationReplayFailureOf entry "final digest mismatch")
  else if entry.entryDigest ≠ entry.recomputedEntryDigest then
    some (obligationReplayFailureOf entry "entry digest mismatch")
  else if !depsClosed entry presentIds then
    some (obligationReplayFailureOf entry "dependency closure failed")
  else
    match payloadFailureReason? entry with
    | some reason => some (obligationReplayFailureOf entry reason)
    | none => none

private def isDependencyFailure (failure : ObligationReplayFailure) : Bool :=
  containsText failure.reason "dependency"

private def isPayloadFailure (failure : ObligationReplayFailure) : Bool :=
  !(isDependencyFailure failure)

def ObligationReplayReport.ofBundle (bundle : ObligationSliceBundle) : ObligationReplayReport :=
  Id.run do
    let presentIds := bundle.entries.map (·.id)
    let mut checked := 0
    let mut passed := 0
    let mut skippedBlocked := 0
    let mut skippedUnclassified := 0
    let mut failures : Array ObligationReplayFailure := #[]
    for entry in bundle.entries do
      match entry.status with
      | .blocked =>
          skippedBlocked := skippedBlocked + 1
      | .unclassified =>
          skippedUnclassified := skippedUnclassified + 1
      | .supported =>
          checked := checked + 1
          match replaySupportedEntry entry presentIds with
          | none => passed := passed + 1
          | some failure => failures := failures.push failure
    let dependencyFailures := failures.foldl (fun acc failure => if isDependencyFailure failure then acc + 1 else acc) 0
    let payloadFailures := failures.foldl (fun acc failure => if isPayloadFailure failure then acc + 1 else acc) 0
    {
      checked := checked
      passed := passed
      failed := failures.size
      skippedBlocked := skippedBlocked
      skippedUnclassified := skippedUnclassified
      bundleDigestValid := bundle.bundleDigestValid
      dependencyFailures := dependencyFailures
      payloadFailures := payloadFailures
      failures := failures
    }

end HeytingLean.KernelAssurance
