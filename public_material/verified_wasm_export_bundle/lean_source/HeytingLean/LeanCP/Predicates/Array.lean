import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.Store

/-!
# LeanCP Array Predicate

`arrayAt addr vs` asserts that the heap contains a contiguous array of values
starting at address `addr`. Each value occupies one heap cell.
-/

namespace HeytingLean.LeanCP

/-- Contiguous array: `arrayAt addr vs` maps `addr+i ↦ vs[i]` for each index i. -/
def arrayAt : Nat → List CVal → HProp
  | _, [] => HProp.emp
  | addr, v :: vs => store addr v ∗ arrayAt (addr + 1) vs

theorem arrayAt_nil (addr : Nat) (h : Heap) :
    arrayAt addr [] h ↔ h = Heap.empty := by
  simp [arrayAt, HProp.emp]

theorem arrayAt_cons (addr : Nat) (v : CVal) (vs : List CVal) (h : Heap) :
    arrayAt addr (v :: vs) h ↔ (store addr v ∗ arrayAt (addr + 1) vs) h := by
  simp [arrayAt]

end HeytingLean.LeanCP
