import HeytingLean.KernelAssurance.Coverage
import HeytingLean.LoF.ICCKernel.Faithfulness

namespace HeytingLean.KernelAssurance

open Lean
open HeytingLean.LoF.ICCKernel

structure ReplayFailure where
  moduleName : String
  declName : String
  reason : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

structure ReplayReport where
  checked : Nat
  passed : Nat
  failed : Nat
  skippedBlocked : Nat
  skippedUnclassified : Nat
  bundleDigestValid : Bool
  failures : Array ReplayFailure
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def replayFailureOf (entry : SliceEntry) (reason : String) : ReplayFailure :=
  { moduleName := entry.moduleName, declName := entry.declName, reason := reason }

private def replaySupportedEntry (entry : SliceEntry) : Option ReplayFailure :=
  if entry.exportedDigest ≠ exportedDeclDigest entry.exported then
    some (replayFailureOf entry "exported digest mismatch")
  else if entry.entryDigest ≠ entry.recomputedEntryDigest then
    some (replayFailureOf entry "entry digest mismatch")
  else if entry.termCounts != entry.exported.termCounts then
    some (replayFailureOf entry "term counts mismatch")
  else
    match recoverAndRelowerExportedDecl entry.exported with
    | .ok lowered =>
        if lowered == entry.exported then
          none
        else
          some (replayFailureOf entry "recover-and-relower changed the exported declaration")
    | .error err =>
        some (replayFailureOf entry s!"recover-and-relower failed: {err.message}")

def ReplayReport.ofBundle (bundle : SliceBundle) : ReplayReport :=
  Id.run do
    let mut checked := 0
    let mut passed := 0
    let mut skippedBlocked := 0
    let mut skippedUnclassified := 0
    let mut failures : Array ReplayFailure := #[]
    for entry in bundle.entries do
      match entry.status with
      | .blocked =>
          skippedBlocked := skippedBlocked + 1
      | .unclassified =>
          skippedUnclassified := skippedUnclassified + 1
      | .supported =>
          checked := checked + 1
          match replaySupportedEntry entry with
          | none => passed := passed + 1
          | some failure => failures := failures.push failure
    {
      checked := checked
      passed := passed
      failed := failures.size
      skippedBlocked := skippedBlocked
      skippedUnclassified := skippedUnclassified
      bundleDigestValid := bundle.bundleDigestValid
      failures := failures
    }

end HeytingLean.KernelAssurance
