import Mathlib.Data.Set.Basic

/-!
# Information as distinction: primitive layer

This module provides a small, executable core for the slogan

> “Information is distinction.”

We deliberately avoid reusing the identifier `Distinction` here, because the repo already
defines an inside/outside carrier `HeytingLean.Numbers.Surreal.LoFDerivation.Distinction`.
Instead we model the primitive “two-sided choice” as `Side`.

The second bridge in this file is a tiny set-theoretic model: `Set Unit` has exactly two
extensional inhabitants (the empty set and the singleton `{()}`), hence is equivalent to `Bool`.
-/

namespace HeytingLean
namespace Information

/-! ## A primitive two-sided carrier -/

/-- The primitive inside/outside choice, kept intentionally small and computable. -/
inductive Side where
  | inside
  | outside
deriving DecidableEq, Repr

namespace Side

def toBool : Side → Bool
  | inside => true
  | outside => false

def ofBool : Bool → Side
  | true => inside
  | false => outside

/-- `Side` is equivalent to `Bool` (a one-bit distinction). -/
def equivBool : Side ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

@[simp] lemma equivBool_apply_inside : equivBool Side.inside = true := rfl
@[simp] lemma equivBool_apply_outside : equivBool Side.outside = false := rfl

@[simp] lemma ofBool_toBool (s : Side) : ofBool (toBool s) = s :=
  equivBool.left_inv s

@[simp] lemma toBool_ofBool (b : Bool) : toBool (ofBool b) = b :=
  equivBool.right_inv b

end Side

/-! ## A minimal “empty vs singleton” set-theoretic model -/

open Set

/-- Interpret a bit as a subset of `Unit`: `false ↦ ∅`, `true ↦ {()}`. -/
noncomputable def boolToSetUnit : Bool → Set Unit
  | true => Set.univ
  | false => (∅ : Set Unit)

/-- Interpret a subset of `Unit` as a bit, by membership of the unique inhabitant. -/
noncomputable def setUnitToBool (s : Set Unit) : Bool := by
  classical
  exact if (() : Unit) ∈ s then true else false

/-- `Bool` is equivalent to `Set Unit` (extensional subsets of a one-point type). -/
noncomputable def boolEquivSetUnit : Bool ≃ Set Unit where
  toFun := boolToSetUnit
  invFun := setUnitToBool
  left_inv := by
    intro b
    classical
    cases b <;> simp [boolToSetUnit, setUnitToBool]
  right_inv := by
    intro s
    classical
    ext u
    cases u
    by_cases h : (() : Unit) ∈ s
    · simp [setUnitToBool, boolToSetUnit, h]
    · simp [setUnitToBool, boolToSetUnit, h]

@[simp] lemma boolEquivSetUnit_apply_true : boolEquivSetUnit true = (Set.univ : Set Unit) := rfl
@[simp] lemma boolEquivSetUnit_apply_false : boolEquivSetUnit false = (∅ : Set Unit) := rfl

end Information
end HeytingLean
