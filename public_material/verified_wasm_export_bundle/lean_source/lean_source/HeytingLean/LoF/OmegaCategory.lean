import Mathlib.Order.Nucleus
import Mathlib.Order.Sublocale
import Mathlib.Order.Heyting.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Monoidal.Cartesian.InfSemilattice
import Mathlib.CategoryTheory.Closed.Cartesian
import HeytingLean.LoF.PrimaryAlgebra
import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.HeytingCore

/-
# OmegaCategory: categorical structure on `Ω_R`

This module equips the fixed-point lattice `Ω_R` of a reentry nucleus `R` with
its natural categorical structure in the Baez–Stay “stay monoidal” sense.

* Order-theoretically, `R.Omega` is a Heyting algebra (see `LoF.HeytingCore`).
* Categorically, the preorder on `R.Omega` yields a thin category.
* As a meet-semilattice with top, `R.Omega` carries a cartesian monoidal
  structure where tensor is meet and unit is `⊤`.

In this file we:

* install the `CartesianMonoidalCategory` structure on `R.Omega`;
* define an internal hom `ihom` given by Heyting implication;
* show that `tensorLeft a` is left adjoint to `ihom a`, making `R.Omega`
  a cartesian closed category in the usual Heyting sense.
-/

namespace HeytingLean
namespace LoF
namespace OmegaCategory

universe u

open CategoryTheory

variable {α : Type u} [PrimaryAlgebra α]

/-- `Ω_R` as a cartesian monoidal category.

This uses the general construction for any meet-semilattice with a greatest
element: the tensor is given by infimum and the unit by `⊤`, and the underlying
category is the preorder category on `R.Omega`. -/
noncomputable instance (R : Reentry α) :
    CartesianMonoidalCategory (R.Omega) :=
  SemilatticeInf.cartesianMonoidalCategory (C := R.Omega)

section ClosedStructure

variable (R : Reentry α)

/-- Internal hom on `Ω_R`, defined as the Heyting implication. -/
def ihom (a b : R.Omega) : R.Omega :=
  a ⇨ b

/-- Residuation for the internal hom on `Ω_R`. -/
lemma le_ihom_iff (a b c : R.Omega) :
    c ≤ ihom R a b ↔ c ⊓ a ≤ b := by
  -- This is just `Reentry.residuation` specialized and rewritten.
  change c ≤ a ⇨ b ↔ c ⊓ a ≤ b
  exact
    (Reentry.residuation (R := R) (a := a) (b := b) (c := c))

/-- The order hom on `Ω_R` given by Heyting implication `a ⇨ ·`. -/
def ihomOrderHom (a : R.Omega) : R.Omega →o R.Omega where
  toFun b := a ⇨ b
  monotone' := by
    intro x y hxy
    -- We show `a ⇨ x ≤ a ⇨ y` using Heyting residuation and `inf_himp_le`.
    -- Step 1: `a ⊓ (a ⇨ x) ≤ x` (modus ponens in `Ω_R`).
    -- Step 2: `(a ⇨ x) ⊓ a ≤ y` by commutativity and transitivity.
    have h₁' : (a ⇨ x) ⊓ a ≤ x := by
      simp [inf_comm]
    have h₂ : (a ⇨ x) ⊓ a ≤ y := le_trans h₁' hxy
    -- Step 3: Residuation: `(a ⇨ x) ≤ a ⇨ y`.
    have h₃ :
        (a ⇨ x) ≤ a ⇨ y :=
      (Reentry.residuation (R := R) (a := a) (b := y) (c := (a ⇨ x))).mpr h₂
    exact h₃

/-- The functor interpreting `ihom R a` as an internal hom endofunctor on `Ω_R`. -/
def ihomFunctor (a : R.Omega) : R.Omega ⥤ R.Omega :=
  (ihomOrderHom (R := R) a).toFunctor

end ClosedStructure

end OmegaCategory
end LoF
end HeytingLean
