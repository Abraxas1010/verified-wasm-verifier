import HeytingLean.KernelAssurance.Replay

namespace HeytingLean.KernelAssurance

open Lean

structure CheckerFailure where
  moduleName : String
  declName : String
  reason : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

structure CheckerReport where
  checked : Nat
  passed : Nat
  failed : Nat
  bundleDigestValid : Bool
  tamperFailures : Nat
  classificationFailures : Nat
  countFailures : Nat
  failures : Array CheckerFailure
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def checkerFailureOf (entry : SliceEntry) (reason : String) : CheckerFailure :=
  { moduleName := entry.moduleName, declName := entry.declName, reason := reason }

private def containsText (haystack needle : String) : Bool :=
  decide ((haystack.splitOn needle).length > 1)

private def checkEntry (entry : SliceEntry) : Array CheckerFailure :=
  let family := familyOfDecl entry.exported
  let status := statusOfDecl entry.exported
  let recomputedExportedDigest := exportedDeclDigest entry.exported
  let recomputedTermCounts := entry.exported.termCounts
  let expectedModuleName := moduleNameText entry.exported
  let expectedDeclName := declNameText entry.exported
  let expectedEntryDigest :=
    mkEntryDigest expectedModuleName expectedDeclName entry.exported.kindTag family status
      recomputedTermCounts recomputedExportedDigest
  let failures0 : Array CheckerFailure := #[]
  let failures1 :=
    if entry.exportedDigest = recomputedExportedDigest then
      failures0
    else
      failures0.push (checkerFailureOf entry "exported digest mismatch")
  let failures2 :=
    if entry.entryDigest = expectedEntryDigest then
      failures1
    else
      failures1.push (checkerFailureOf entry "entry digest mismatch")
  let failures3 :=
    if entry.moduleName = expectedModuleName ∧ entry.declName = expectedDeclName then
      failures2
    else
      failures2.push (checkerFailureOf entry "entry name metadata mismatch")
  let failures4 :=
    if entry.kindTag = entry.exported.kindTag ∧ entry.family = family ∧ entry.status = status then
      failures3
    else
      failures3.push (checkerFailureOf entry "family or status classification mismatch")
  let failures5 :=
    if entry.termCounts == recomputedTermCounts then
      failures4
    else
      failures4.push (checkerFailureOf entry "term counts mismatch")
  failures5

private def isTamperFailure (failure : CheckerFailure) : Bool :=
  containsText failure.reason "digest" || containsText failure.reason "metadata"

private def isClassificationFailure (failure : CheckerFailure) : Bool :=
  containsText failure.reason "classification"

private def isCountFailure (failure : CheckerFailure) : Bool :=
  containsText failure.reason "counts"

def CheckerReport.ofBundle (bundle : SliceBundle) : CheckerReport :=
  Id.run do
    let mut failures : Array CheckerFailure := #[]
    for entry in bundle.entries do
      failures := failures ++ checkEntry entry
    let tamperFailures := failures.foldl (fun acc failure => if isTamperFailure failure then acc + 1 else acc) 0
    let classificationFailures := failures.foldl (fun acc failure => if isClassificationFailure failure then acc + 1 else acc) 0
    let countFailures := failures.foldl (fun acc failure => if isCountFailure failure then acc + 1 else acc) 0
    {
      checked := bundle.entries.size
      passed := bundle.entries.size - failures.size
      failed := failures.size
      bundleDigestValid := bundle.bundleDigestValid
      tamperFailures := tamperFailures
      classificationFailures := classificationFailures
      countFailures := countFailures
      failures := failures
    }

end HeytingLean.KernelAssurance
