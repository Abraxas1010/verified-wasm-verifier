import HeytingLean.Magma.Separation.MSS

namespace HeytingLean.Magma.Bridge

open HeytingLean.Magma
open HeytingLean.Magma.Separation

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]
  [SeparationPresentation A]

theorem scale_invariance_triple_equivalence (φ : Magma A → Prop) :
    ScaleInvariant (A := A) φ ↔
      MagmaticClass (A := A) { x | φ x } ∧
      (∀ u0 : Magma A, (∃ x, x ∈ u0 ∧ φ x) →
        ∃ m : Magma A, ∀ x : Magma A, x ∈ m ↔ x ∈ u0 ∧ φ x) := by
  constructor
  · intro hφ
    refine ⟨hφ, ?_⟩
    intro u0 hNonempty
    exact magmatic_separation_scheme φ hφ u0 hNonempty
  · rintro ⟨hMag, _⟩
    exact hMag

end HeytingLean.Magma.Bridge
