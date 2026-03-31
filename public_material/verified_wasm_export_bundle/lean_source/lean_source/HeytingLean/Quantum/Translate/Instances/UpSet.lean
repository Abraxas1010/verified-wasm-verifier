import Mathlib.Data.Set.Lattice
import HeytingLean.Quantum.OML.Examples.O6
import HeytingLean.Quantum.Translate.{Modality,Core,Omega,RT}

open scoped Classical

namespace HeytingLean.Quantum.Translate

namespace UpSet

def idNucleus (α : Type _) [SemilatticeInf α] : Nucleus α :=
{ toInfHom :=
    { toFun := id
      map_inf' := by intro a b; rfl }
  le_apply' := by intro a; exact le_rfl
  idempotent' := by intro a; rfl }

variable {β : Type _}

open HeytingLean.Quantum.OML O6

def M_SetO6 : Modality (Set O6) :=
  { J := idNucleus (Set O6)
    preserves_top := by rfl }

def trUp (a : O6) : Set O6 := { x | a ≤ x }

lemma trUp_inf (a b : O6) : trUp (a ⊓ b) = (trUp a) ∩ (trUp b) := by
  ext x; constructor
  · intro hx; rcases hx with hx; -- hx : a ⊓ b ≤ x
    have h : a ≤ x ∧ b ≤ x := by
      have := O6.le_inf_iff (x := a) (y := b) (z := x)
      -- rewrite iff from lemma
      have : a ≤ O6.inf b x ↔ _ := rfl; clear this
      -- Use provided iff: x ≤ inf y z ↔ x ≤ y ∧ x ≤ z
      -- We need the converse form; so apply the iff with x := a ∧ b
      exact (O6.le_inf_iff).1 hx
    exact ⟨h.left, h.right⟩
  · intro hx
    rcases hx with ⟨ha, hb⟩
    -- need a ⊓ b ≤ x; use le_inf_iff converse
    exact (O6.le_inf_iff).2 ⟨ha, hb⟩

lemma trUp_sup_le (a b : O6) : trUp (a ⊔ b) ⊆ (trUp a) ∪ (trUp b) := by
  intro x hx
  -- a ⊔ b ≤ x ⇒ (a ≤ x ∧ b ≤ x) ⇒ x ∈ up a ∩ up b ⊆ up a ∪ up b
  have h : a ≤ x ∧ b ≤ x := (O6.sup_le_iff).1 hx
  exact Or.inl h.left -- in fact x is in both; choose left

def O6UpQLMap : QLMap O6 (Set O6) where
  M := M_SetO6
  tr := trUp
  map_inf := by
    intro x y; simp [trUp_inf]
  map_sup_le := by
    intro x y; -- J is id, so closure is identity
    change (trUp (x ⊔ y)) ⊆ (trUp x) ∪ (trUp y)
    exact trUp_sup_le x y

end UpSet

end HeytingLean.Quantum.Translate
