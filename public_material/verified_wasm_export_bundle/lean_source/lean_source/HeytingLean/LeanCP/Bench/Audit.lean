import HeytingLean.LeanCP.Bench.Registry

namespace HeytingLean.LeanCP.Bench

def domainCount (domain : BenchDomain) : Nat :=
  countedEntries.countP (fun entry => entry.domain = domain)

def totalCount : Nat :=
  countedEntries.length

def allTopLevel : Bool :=
  countedEntries.all (fun entry => entry.entryKind = "topLevel")

theorem totalCount_ge_50 : 50 ≤ totalCount := by
  native_decide

theorem scalarArith_floor : 8 ≤ domainCount .scalarArith := by
  native_decide

theorem arraySearchSort_floor : 8 ≤ domainCount .arraySearchSort := by
  native_decide

theorem linkedHeap_floor : 8 ≤ domainCount .linkedHeap := by
  native_decide

theorem treeHash_floor : 8 ≤ domainCount .treeHash := by
  native_decide

theorem callsControlRec_floor : 8 ≤ domainCount .callsControlRec := by
  native_decide

theorem stringMemorySystem_floor : 8 ≤ domainCount .stringMemorySystem := by
  native_decide

theorem allTopLevel_ok : allTopLevel = true := by
  native_decide

end HeytingLean.LeanCP.Bench
