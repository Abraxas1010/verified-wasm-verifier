import HeytingLean.Numbers.Surreal.ClosureReentry

/-!
# Surreal.ReentryFixedPoint

SN-020 baseline: explicit fixed-point and oscillation operators for the
Surreal closure-reentry lane.

Core operator:
- `step S := S ∪ canonicalCore`

This file proves:
- fixed-point characterization (`step S = S ↔ canonicalCore ⊆ S`),
- least fixed-point theorem (`canonicalCore`),
- a two-step oscillation law from the empty carrier.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Set
open HeytingLean.Numbers.SurrealCore

abbrev Carrier := Set PreGame

/-- Closure-reentry step operator. -/
def step (S : Carrier) : Carrier := closureCore S

/-- Unfolding equation for the closure-reentry step. -/
@[simp] theorem step_eq_union (S : Carrier) : step S = S ∪ canonicalCore := rfl

/-- Complement-after-closure oscillation step. -/
def oscillate (S : Carrier) : Carrier := (step S)ᶜ

/-- Fixed points of the closure-reentry step. -/
def FixedPoints : Set Carrier := { S | step S = S }

theorem step_fixed_iff_core_subset (S : Carrier) :
    step S = S ↔ canonicalCore ⊆ S := by
  constructor
  · intro hfix x hxC
    have hxStep : x ∈ step S := by
      show x ∈ S ∪ canonicalCore
      exact Or.inr hxC
    exact hfix ▸ hxStep
  · intro hCore
    ext x
    constructor
    · intro hx
      change x ∈ S ∪ canonicalCore at hx
      rcases hx with hxS | hxC
      · exact hxS
      · exact hCore hxC
    · intro hxS
      change x ∈ S ∪ canonicalCore
      exact Or.inl hxS

theorem canonicalCore_fixed : step canonicalCore = canonicalCore := by
  exact (step_fixed_iff_core_subset canonicalCore).2 (by intro x hx; exact hx)

theorem canonicalCore_mem_fixed : canonicalCore ∈ FixedPoints := by
  simp [FixedPoints]

/-- Least fixed-point theorem for `step`. -/
theorem canonicalCore_isLeast_fixed : IsLeast FixedPoints canonicalCore := by
  refine ⟨canonicalCore_mem_fixed, ?_⟩
  intro S hS
  exact (step_fixed_iff_core_subset S).1 hS

theorem oscillate_empty_eq_core_compl :
    oscillate (∅ : Carrier) = canonicalCoreᶜ := by
  ext x
  simp [oscillate, step_eq_union]

/-- Nontrivial oscillation theorem: two oscillation steps from `∅` return to `∅`. -/
theorem oscillate_twice_empty :
    oscillate (oscillate (∅ : Carrier)) = (∅ : Carrier) := by
  calc
    oscillate (oscillate (∅ : Carrier))
        = oscillate (canonicalCoreᶜ : Carrier) := by
            simp [oscillate_empty_eq_core_compl]
    _ = (Set.univ : Carrier)ᶜ := by
          ext x
          simp [oscillate, step_eq_union]
    _ = (∅ : Carrier) := by simp

end Surreal
end Numbers
end HeytingLean
