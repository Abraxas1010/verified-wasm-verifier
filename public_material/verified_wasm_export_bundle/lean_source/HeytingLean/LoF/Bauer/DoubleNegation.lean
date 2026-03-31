import Mathlib.Order.Heyting.Regular
import Mathlib.Order.Nucleus

/-!
# Bauer: double-negation (Booleanization) nucleus

This module provides the **double-negation nucleus** `a ↦ ¬¬a` on any Heyting algebra,
and records the associated “classical core” as the Boolean algebra of Heyting-regular elements.

This is the standard topos-theoretic **double-negation topology** / Booleanization step,
and it is one of the key mechanisms used in synthetic computability theory: one can reason
classically about *regular* propositions while staying in an intuitionistic meta-theory.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

open Heyting

universe u

variable (α : Type u) [HeytingAlgebra α]

/-- The **double-negation nucleus** on a Heyting algebra: `a ↦ aᶜᶜ` (i.e. `¬¬a`). -/
def doubleNegNucleus : Nucleus α where
  toFun a := aᶜᶜ
  map_inf' a b := by
    simpa using (compl_compl_inf_distrib (a := a) (b := b))
  idempotent' a := by
    -- `(¬¬a)` is regular because it is the complement of `¬a`.
    exact le_of_eq (IsRegular.eq (isRegular_compl (a := aᶜ)))
  le_apply' a := le_compl_compl

@[simp] lemma doubleNegNucleus_apply (a : α) : doubleNegNucleus α a = aᶜᶜ := rfl

/-- Fixed points of `doubleNegNucleus` are exactly the Heyting-regular elements. -/
@[simp] lemma doubleNegNucleus_fixed_iff (a : α) :
    doubleNegNucleus α a = a ↔ IsRegular a := Iff.rfl

/-- The Boolean algebra of Heyting-regular elements, i.e. the “classical core”. -/
abbrev ClassicalCore : Type u :=
  Regular α

instance : BooleanAlgebra (ClassicalCore α) := by
  dsimp [ClassicalCore]
  infer_instance

/-- Regularization map into the classical core: `a ↦ ⟨¬¬a, _⟩`. -/
abbrev toClassicalCore : α →o ClassicalCore α :=
  Regular.toRegular

@[simp] lemma coe_toClassicalCore (a : α) :
    ((toClassicalCore α a : ClassicalCore α) : α) = doubleNegNucleus α a := rfl

/-- The range presentation of the classical core: the range of `doubleNegNucleus` is equivalent to `Regular α`. -/
noncomputable def rangeDoubleNegEquivClassicalCore :
    Set.range (doubleNegNucleus α) ≃ ClassicalCore α := by
  classical
  refine
    { toFun := fun x => ?_
      invFun := fun x => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨x.1, ?_⟩
    rcases x.2 with ⟨a, ha⟩
    -- `¬¬a` is regular because it is the complement of `¬a`, then transport along `ha`.
    have hx : IsRegular (doubleNegNucleus α a) := by
      change IsRegular ((aᶜ : α)ᶜ)
      exact isRegular_compl (a := (aᶜ : α))
    simpa [ha] using hx
  · refine ⟨x.1, ?_⟩
    refine ⟨x.1, ?_⟩
    -- Regular elements satisfy `¬¬x = x`.
    simpa [doubleNegNucleus, Heyting.IsRegular] using x.2
  · intro x
    apply Subtype.ext
    rfl
  · intro x
    apply Subtype.ext
    rfl

end Bauer
end LoF
end HeytingLean
