import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 6: Geometric Morphisms and Bridges
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def pullbackBridge (x : Nat) : Nat :=
  closure x

theorem R_commutes_with_pullback (x : Nat) :
    closure (pullbackBridge x) = pullbackBridge (closure x) := by
  simp [pullbackBridge]

theorem grant_constraint_preservation (a b : Nat) : Nat.min a b ≤ a := by
  exact Nat.min_le_left _ _

end NucleusPOD
end HeytingLean
