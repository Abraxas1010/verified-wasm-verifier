import HeytingLean.LeanCP.Core.HProp

/-!
# LeanCP Store Predicate

The primitive points-to predicate: `store addr v` asserts that the heap
contains exactly the single cell `addr ↦ v`.
-/

namespace HeytingLean.LeanCP

/-- `store addr v`: the heap is exactly the singleton `{addr ↦ v}`. -/
def store (addr : Nat) (v : CVal) : HProp := HProp.pointsTo addr v

/-- Contiguous block predicate starting at `addr`. -/
def blockAt (addr : Nat) : List CVal → HProp
  | [] => HProp.emp
  | v :: vs => store addr v ∗ blockAt (addr + 1) vs

/-- Freshly allocated block of `cells` uninitialized cells. -/
def undefBlock (addr cells : Nat) : HProp :=
  blockAt addr (List.replicate cells CVal.undef)

end HeytingLean.LeanCP
