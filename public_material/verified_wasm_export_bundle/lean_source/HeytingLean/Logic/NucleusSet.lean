import Mathlib.Data.Set.Lattice
import Mathlib.Order.Nucleus
import HeytingLean.Logic.TransfiniteNucleus

open Set

namespace HeytingLean
namespace Logic

variable {σ : Type*}

/-- A simple closure nucleus on sets: `S ↦ S ∪ U`. -/
def addClosure (U : Set σ) : Nucleus (Set σ) where
  toFun S := S ∪ U
  map_inf' S T := by
    ext x; constructor
    · intro hx
      rcases hx with hxST | hxU
      · exact And.intro (Or.inl hxST.1) (Or.inl hxST.2)
      · exact And.intro (Or.inr hxU) (Or.inr hxU)
    · intro hx
      rcases hx with ⟨hS, hT⟩
      cases hS with
      | inl hS =>
        cases hT with
        | inl hT => exact Or.inl ⟨hS, hT⟩
        | inr hU => exact Or.inr hU
      | inr hU => exact Or.inr hU
  idempotent' S := by
    intro x hx
    rcases hx with hxSU | hxU
    · cases hxSU with
      | inl hS => exact Or.inl hS
      | inr hU => exact Or.inr hU
    · exact Or.inr hxU
  le_apply' S := by
    intro x hx; exact Or.inl hx

section Lemmas

variable (U : Set σ)

lemma iterateNat_one (S : Set σ) :
    iterateNat (addClosure (σ := σ) U) 1 S = S ∪ U := by
  ext x; simp [iterateNat, addClosure]

lemma iterateNat_two_eq_one (S : Set σ) :
    iterateNat (addClosure (σ := σ) U) 2 S =
    iterateNat (addClosure (σ := σ) U) 1 S := by
  ext x; simp [iterateNat, addClosure, Set.union_assoc, Set.union_left_comm, Set.union_comm]

end Lemmas

end Logic
end HeytingLean
