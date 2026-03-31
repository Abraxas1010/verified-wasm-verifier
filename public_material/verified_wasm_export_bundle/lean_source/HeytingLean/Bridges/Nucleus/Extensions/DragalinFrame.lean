import HeytingLean.Bridges.Nucleus.Extensions.UniformCompletionNucleus

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

open Set

universe u

/-- Path-based frame data used to generate a nucleus lane. -/
structure DragalinFrame (α : Type u) where
  Path : α → α → Prop
  core : Set α
  path_refl : Reflexive Path
  path_trans : Transitive Path
  core_backward_closed : ∀ {x y}, Path x y → y ∈ core → x ∈ core

namespace DragalinFrame

variable {α : Type u}

/-- Closure-generated core from path reachability into the distinguished core. -/
def generatedCore (F : DragalinFrame α) : Set α :=
  {x | ∃ y, y ∈ F.core ∧ F.Path x y}

theorem core_subset_generatedCore (F : DragalinFrame α) : F.core ⊆ F.generatedCore := by
  intro x hx
  exact ⟨x, hx, F.path_refl x⟩

/-- Reachability closure is stable under backward path composition. -/
theorem generatedCore_backward_closed (F : DragalinFrame α)
    {x y : α} (hxy : F.Path x y) (hy : y ∈ F.generatedCore) : x ∈ F.generatedCore := by
  rcases hy with ⟨z, hz, hyz⟩
  exact ⟨z, hz, F.path_trans hxy hyz⟩

/-- Nucleus induced from the generated core via adjoin-closure. -/
def generatedNucleus (F : DragalinFrame α) : _root_.Nucleus (Set α) :=
  sequenceCompletionNucleus (α := α) F.generatedCore

@[simp] theorem generatedNucleus_apply (F : DragalinFrame α) (U : Set α) :
    F.generatedNucleus U = U ∪ F.generatedCore := by
  exact sequenceCompletionNucleus_apply (α := α) F.generatedCore U

/-- The generated core is fixed under its induced nucleus. -/
theorem generatedCore_fixed (F : DragalinFrame α) :
    F.generatedNucleus F.generatedCore = F.generatedCore := by
  simp [generatedNucleus]

end DragalinFrame

end Extensions
end Nucleus
end Bridges
end HeytingLean
