import HeytingLean.LoF.Bauer.SyntheticComputability

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

open Set

universe u

/-- Sequence-style completion nucleus on predicates: adjoin the completion core. -/
def sequenceCompletionNucleus {α : Type u} (core : Set α) : _root_.Nucleus (Set α) :=
  HeytingLean.LoF.Bauer.SyntheticComputability.Predicate.adjoinNucleus (ι := α) core

@[simp] theorem sequenceCompletionNucleus_apply {α : Type u} (core U : Set α) :
    sequenceCompletionNucleus (α := α) core U = U ∪ core := by
  unfold sequenceCompletionNucleus
  exact
    (HeytingLean.LoF.Bauer.SyntheticComputability.Predicate.adjoinNucleus_apply
      (ι := α) core U)

/-- Scoped completion interface for a carrier. -/
structure UniformCompletionModel (α : Type u) where
  cauchyCore : Set α
  completed : Set α
  core_le_completed : cauchyCore ⊆ completed

namespace UniformCompletionModel

variable {α : Type u}

/-- Nucleus induced by the chosen completion core. -/
def inducedNucleus (M : UniformCompletionModel α) : _root_.Nucleus (Set α) :=
  sequenceCompletionNucleus (α := α) M.completed

/-- Characterization of fixed points for the induced completion nucleus. -/
theorem fixed_iff_contains_completed (M : UniformCompletionModel α) (U : Set α) :
    inducedNucleus M U = U ↔ M.completed ⊆ U := by
  unfold inducedNucleus sequenceCompletionNucleus
  exact
    (HeytingLean.LoF.Bauer.SyntheticComputability.Predicate.adjoinNucleus_fixed_iff
      (ι := α) M.completed U)

/-- The completed core is fixed under the induced completion nucleus. -/
theorem completed_fixed (M : UniformCompletionModel α) :
    inducedNucleus M M.completed = M.completed :=
  (fixed_iff_contains_completed (M := M) M.completed).2 subset_rfl

/-- The Cauchy core is contained in the completed core by model assumption. -/
theorem cauchyCore_le_completed (M : UniformCompletionModel α) :
    M.cauchyCore ⊆ M.completed :=
  M.core_le_completed

end UniformCompletionModel

end Extensions
end Nucleus
end Bridges
end HeytingLean
