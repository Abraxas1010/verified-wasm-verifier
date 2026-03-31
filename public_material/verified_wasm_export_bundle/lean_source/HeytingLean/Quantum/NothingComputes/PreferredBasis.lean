import HeytingLean.Genesis.NothingComputes.YWitnessStrengthened
import HeytingLean.Bridge.YWitness.ClassicalConstructive

namespace HeytingLean.Quantum.NothingComputes

open HeytingLean.LoF.Bauer

/-- Preferred-basis candidates are exactly the double-negation fixed points selected by the
relevant nucleus.
-/
def BasisCandidate (α : Type _) [HeytingAlgebra α] (a : α) : Prop :=
  Function.IsFixedPt (doubleNegNucleus α) a

/-- The preferred selector associated to the Boolean-core lane. -/
def preferredSelector (α : Type _) [HeytingAlgebra α] (a : α) : α :=
  doubleNegNucleus α a

theorem preferredSelector_is_basisCandidate (α : Type _) [HeytingAlgebra α] (a : α) :
    BasisCandidate α (preferredSelector α a) := by
  simpa [BasisCandidate, preferredSelector] using
    HeytingLean.Bridge.YWitness.y_fixed_point_shape_on_dn_core (α := α) a

/-- Two distinct basis candidates already constitute a nontrivial many-eigenform family at the
algebraic level.
-/
structure EigenformFamily (α : Type _) [HeytingAlgebra α] where
  left : α
  right : α
  left_fixed : BasisCandidate α left
  right_fixed : BasisCandidate α right
  distinct : left ≠ right

theorem many_eigenforms_of_distinct_candidates
    (α : Type _) [HeytingAlgebra α] {x y : α}
    (hx : BasisCandidate α x) (hy : BasisCandidate α y) (hxy : x ≠ y) :
    Nonempty (EigenformFamily α) := by
  exact ⟨⟨x, y, hx, hy, hxy⟩⟩

end HeytingLean.Quantum.NothingComputes
