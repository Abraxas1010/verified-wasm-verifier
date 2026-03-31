import HeytingLean.Information.Primitive
import HeytingLean.LoF.Nucleus

/-!
# Information as distinction: dynamics layer

This module defines a tiny “oscillation” (a two-state flip) and a fuel-bounded runner that
searches for a stable state.

Because `Reentry` nuclei are idempotent, “apply `R` until stable” is usually trivial. To keep the
runtime story non-degenerate (even for the common identity nucleus), we expose a stability
predicate that also checks the re-entry support window.
-/

namespace HeytingLean
namespace Information

open HeytingLean.LoF
open scoped Classical

/-- A two-state “information oscillation”. -/
inductive InfoState where
  | primordial
  | counter
deriving DecidableEq, Repr

namespace InfoState

/-- One step of the oscillation: flip the state. -/
def step : InfoState → InfoState
  | primordial => counter
  | counter => primordial

@[simp] lemma step_primordial : step primordial = counter := rfl
@[simp] lemma step_counter : step counter = primordial := rfl

@[simp] lemma step_step (s : InfoState) : step (step s) = s := by
  cases s <;> rfl

end InfoState

/-! ## Stability predicates -/

/-- “Fixed point” stability: the element is fixed by the re-entry nucleus. -/
def IsFixed {α : Type _} [PrimaryAlgebra α] (R : Reentry α) (a : α) : Prop :=
  R a = a

/-- “Support-window” stability: fixed, non-bottom, and inside the designated support window.

This is the predicate used by `runUntilStable?`.
-/
def IsStable {α : Type _} [PrimaryAlgebra α] (R : Reentry α) (a : α) : Prop :=
  IsFixed R a ∧ ⊥ < a ∧ a ≤ R.support

/-! ## Fuel-bounded runners -/

/-- Attempt to run an oscillation until it reaches a stable state.

Returns `none` if the fuel is exhausted before stability is reached.
-/
noncomputable def runUntilStable?
    {α : Type _} [PrimaryAlgebra α]
    (R : Reentry α) (interpret : InfoState → α) :
    Nat → InfoState → Option (Nat × α)
  | 0, _ => none
  | fuel + 1, s =>
      let a := interpret s
      if _h : IsStable R a then
        some (0, a)
      else
        match runUntilStable? R interpret fuel (InfoState.step s) with
        | none => none
        | some (n, a') => some (n + 1, a')

/-- Total wrapper around `runUntilStable?`.

If fuel is exhausted, we return `(fuel, interpret s)` as a best-effort result.
-/
noncomputable def runUntilStable
    {α : Type _} [PrimaryAlgebra α]
    (R : Reentry α) (interpret : InfoState → α) (fuel : Nat) (s : InfoState) : Nat × α :=
  match runUntilStable? R interpret fuel s with
  | some r => r
  | none => (fuel, interpret s)

end Information
end HeytingLean
