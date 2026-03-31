import Mathlib.Data.Set.Lattice
import HeytingLean.Quantum.OML.Examples.O6
import HeytingLean.Quantum.Translate.{Modality,Core,Omega,RT}

open scoped Classical

namespace HeytingLean.Quantum.Translate

open HeytingLean.Quantum.OML O6

/-- A meet‑preserving (nucleus) closure on `Set O6` adding a fixed closed set `C`. -/
def unionNucleus (C : Set O6) : Nucleus (Set O6) where
  toFun S := S ∪ C
  le_apply' := by
    intro S; exact Set.subset_union_left
  idempotent' := by
    intro S; ext x; constructor <;> intro hx <;> cases hx with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr h
    | inl h => exact Or.inl (Or.inl h)
    | inr h => exact Or.inr h
  map_inf' := by
    intro S T; ext x; constructor
    · intro hx; rcases hx with hx | hx; all_goals
        try exact And.intro (Or.inr hx) (Or.inr hx)
      -- hx : x ∈ S ∩ T
      exact And.intro (Or.inl hx.left) (Or.inl hx.right)
    · intro hx
      rcases hx with ⟨h1, h2⟩
      cases h1 with
      | inl hS =>
        cases h2 with
        | inl hT => exact Or.inl ⟨hS, hT⟩
        | inr hC => exact Or.inr hC
      | inr hC => exact Or.inr hC

/-- Modality on `Set O6` induced by `unionNucleus C`. -/
def M_SetO6_C (C : Set O6) : Modality (Set O6) :=
  { J := unionNucleus C
    preserves_top := by simp }

/-- Principal up‑set translation for `O6`. -/
def trUp (a : O6) : Set O6 := { x | a ≤ x }

lemma trUp_inf (a b : O6) : trUp (a ⊓ b) = (trUp a) ∩ (trUp b) := by
  ext x; constructor
  · intro hx
    have h : a ≤ x ∧ b ≤ x := (O6.le_inf_iff).1 hx
    exact ⟨h.left, h.right⟩
  · intro hx
    exact (O6.le_inf_iff).2 ⟨hx.left, hx.right⟩

lemma trUp_sup_le (a b : O6) : trUp (a ⊔ b) ⊆ (trUp a) ∪ (trUp b) := by
  intro x hx; have h := (O6.sup_le_iff).1 hx; exact Or.inl h.left

/-- Concrete QLMap for `O6` into `(Set O6)` with nucleus `S ↦ S ∪ C`. -/
def O6UpQLMapN (C : Set O6) : QLMap O6 (Set O6) where
  M := M_SetO6_C C
  tr := trUp
  map_inf := by intro x y; simp [trUp_inf]
  map_sup_le := by
    intro x y
    change trUp (x ⊔ y) ⊆ (trUp x ∪ trUp y) ∪ C
    intro z hz; exact Set.subset_union_right _ ((trUp_sup_le x y) hz)

end HeytingLean.Quantum.Translate
