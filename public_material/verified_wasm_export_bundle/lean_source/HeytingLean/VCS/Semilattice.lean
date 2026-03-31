import HeytingLean.VCS.Merge
import Mathlib.Data.Finset.Basic

namespace HeytingLean
namespace VCS

/-- Commutative-idempotent merge carrier used for CRDT reasoning. -/
abbrev MergeCarrier := Finset FileOp

/-- Join operation for concurrent edits. -/
def mergeJoin (x y : MergeCarrier) : MergeCarrier := x ∪ y

/-- Embed a single operation into the merge carrier. -/
def atom (op : FileOp) : MergeCarrier := ({op} : Finset FileOp)

theorem merge_comm (x y : MergeCarrier) :
    mergeJoin x y = mergeJoin y x := by
  simp [mergeJoin, Finset.union_comm]

theorem merge_assoc (x y z : MergeCarrier) :
    mergeJoin (mergeJoin x y) z = mergeJoin x (mergeJoin y z) := by
  simp [mergeJoin, Finset.union_assoc]

theorem merge_idem (x : MergeCarrier) :
    mergeJoin x x = x := by
  simp [mergeJoin]

theorem merge_ops_comm (a b : FileOp) :
    mergeJoin (atom a) (atom b) = mergeJoin (atom b) (atom a) := by
  simpa [atom] using merge_comm (atom a) (atom b)

end VCS
end HeytingLean
