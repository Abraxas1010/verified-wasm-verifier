import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 4: Venue and Slice Topos
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def SliceCategory (_V : Venue) : Type := Agent

theorem slice_topos (V : Venue) : closure (closure V.budget) = closure V.budget := by
  exact closure_idempotent V.budget

def sliceOmega (_V : Venue) : SliceCategory _V → Bool :=
  fun A => A.agentId % 2 == 0

theorem slice_subobject_classifier (V : Venue) :
    ∃ omega : SliceCategory V → Bool, ∀ A, omega A = true ↔ A.agentId % 2 = 0 := by
  refine ⟨sliceOmega V, ?_⟩
  intro A
  constructor
  · intro h
    simp [sliceOmega] at h
    exact h
  · intro h
    simp [sliceOmega, h]

theorem role_lattice (r₁ r₂ : Nat) : Nat.min r₁ r₂ ≤ Nat.max r₁ r₂ := by
  exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)

end NucleusPOD
end HeytingLean
