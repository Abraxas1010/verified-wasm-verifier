import HeytingLean.LoF.Combinators.Rewriting.StepAt

/-!
# Smoke test: `StepAt` (position-aware steps) and disjoint commutation

This file exercises:

* `Comb.Step.exists_stepAt` (every step has a position),
* `Comb.StepAt.commute_of_disjoint` (non-overlapping redexes commute).
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb

open Comb.RedexPath

/-! ## A tiny commuting example -/

namespace Example

-- Build a term with two disjoint redexes: one in the left subtree (a `K`-redex),
-- one in the right subtree (a `Y`-redex).
def a : Comb := .S
def b : Comb := .K
def f : Comb := .K

def tLeft : Comb := Comb.app (Comb.app .K a) b
def tRight : Comb := Comb.app .Y f
def t : Comb := Comb.app tLeft tRight

def u : Comb := Comb.app a tRight
def v : Comb := Comb.app tLeft (Comb.app f (Comb.app .Y f))

-- Positioned one-step reductions at paths `[L]` and `[R]`.
def hK : tLeft.StepAt .K [] a :=
  Comb.StepAt.K_root a b

def hY : tRight.StepAt .Y [] (Comb.app f (Comb.app .Y f)) :=
  Comb.StepAt.Y_root f

def h1 : t.StepAt .K [Dir.L] u :=
  Comb.StepAt.left (a := tRight) hK

def h2 : t.StepAt .Y [Dir.R] v :=
  Comb.StepAt.right (f := tLeft) hY

-- `[L]` and `[R]` are disjoint (neither is a prefix of the other).
theorem disjLR : Disjoint [Dir.L] [Dir.R] := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases h with ⟨r, hr⟩
    -- `[R]` cannot equal `[L] ++ r` since the heads disagree.
    cases r <;> cases hr
  · intro h
    rcases h with ⟨r, hr⟩
    -- `[L]` cannot equal `[R] ++ r` since the heads disagree.
    cases r <;> cases hr

-- The commuting lemma produces a common join.
example : ∃ w : Comb, u.StepAt .Y [Dir.R] w ∧ v.StepAt .K [Dir.L] w :=
  Comb.StepAt.commute_of_disjoint h1 h2 disjLR

end Example

end LoF
end Tests
end HeytingLean
