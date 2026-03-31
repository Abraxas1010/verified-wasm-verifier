import Mathlib.Order.Nucleus
import Mathlib.Data.Set.BooleanAlgebra
import HeytingLean.Numbers.SurrealCore

/-!
# Parametric core-union nuclei on `Set PreGame`

This complements the fixed canonical nucleus with a parametric family
`R_union C : Order.Nucleus (Set PreGame)` acting by `S ↦ S ∪ C`.
It allows simple algebra on “cores” (e.g., meets correspond to
intersection of cores). We keep it separate from the canonical core.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Classical
open Set
open HeytingLean.Numbers.SurrealCore

/-- Core-union nucleus: `S ↦ S ∪ C`. -/
def R_union (C : Set PreGame) : Nucleus (Set PreGame) where
  toFun S := S ∪ C
  le_apply' := by
    intro S; exact subset_union_left
  idempotent' := by
    intro S; intro x hx
    -- ((S ∪ C) ∪ C) ⊆ (S ∪ C)
    rcases hx with hSC | hC
    · -- hSC : x ∈ S ∪ C
      rcases hSC with hS | hC'
      · exact Or.inl hS
      · exact Or.inr hC'
    · exact Or.inr hC
  map_inf' := by
    intro S T; ext x; constructor
    · intro hx
      rcases hx with hx | hx
      · rcases hx with ⟨hS, hT⟩; exact And.intro (Or.inl hS) (Or.inl hT)
      · exact And.intro (Or.inr hx) (Or.inr hx)
    · intro hx
      rcases hx with ⟨h1, h2⟩
      cases h1 with
      | inl hS =>
        cases h2 with
        | inl hT => exact Or.inl ⟨hS, hT⟩
        | inr hC => exact Or.inr hC
      | inr hC => exact Or.inr hC

/-- Monotonicity in the core parameter. -/
lemma R_union_le_of_subset {C D : Set PreGame} (hCD : C ⊆ D) :
    R_union (C := C) ≤ R_union (C := D) := by
  intro S x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (hCD hx)

/-- Meet nucleus acts by union with `C ∩ D`. -/
lemma R_union_inf_act {C D : Set PreGame} (S : Set PreGame) :
  ((R_union (C := C)) ⊓ (R_union (C := D))).toFun S = S ∪ (C ∩ D) := by
  -- Show two inclusions: ≤ via meet ≤ each, ≥ via `R_union (C ∩ D)` ≤ meet.
  apply le_antisymm
  · intro x hx
    -- (inf) acts ≤ each ⇒ x ∈ (S ∪ C) ∧ x ∈ (S ∪ D) ⇒ x ∈ S ∪ (C ∩ D)
    have hx₁ : x ∈ (R_union (C := C)).toFun S := by exact (inf_le_left : ((R_union (C := C)) ⊓ (R_union (C := D))) ≤ (R_union (C := C))) S hx
    have hx₂ : x ∈ (R_union (C := D)).toFun S := by exact (inf_le_right : ((R_union (C := C)) ⊓ (R_union (C := D))) ≤ (R_union (C := D))) S hx
    rcases hx₁ with hS | hC
    · exact Or.inl hS
    · rcases hx₂ with hS | hD
      · exact Or.inl hS
      · exact Or.inr ⟨hC, hD⟩
  · intro x hx
    -- Use `R_union (C ∩ D) ≤` meet then act on S
    have hle : R_union (C := C ∩ D) ≤ (R_union (C := C)) ⊓ (R_union (C := D)) := by
      refine le_inf ?_ ?_
      · exact R_union_le_of_subset (C := C ∩ D) (D := C) (by intro x hx; exact hx.1)
      · exact R_union_le_of_subset (C := C ∩ D) (D := D) (by intro x hx; exact hx.2)
    have hx' : x ∈ (R_union (C := C ∩ D)).toFun S := by
      rcases hx with hS | hCD
      · exact Or.inl hS
      · exact Or.inr hCD
    exact hle S hx'

/-- Fixed points of the core-union nucleus are exactly the supersets of `C`. -/
lemma fix_R_union {C : Set PreGame} {S : Set PreGame} :
    (R_union (C := C)) S = S ↔ C ⊆ S := by
  constructor
  · intro h; exact (union_eq_left.mp h)
  · intro h; exact (union_eq_left.mpr h)

end Surreal
end Numbers
end HeytingLean
