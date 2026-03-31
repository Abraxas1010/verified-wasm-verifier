/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

/-!
# Scale Predicates for Non-Archimedean Fields

This module defines basic "scale" predicates (infinitesimal, infinite, macro)
for ordered fields. These are intended as lightweight building blocks for the
SurrealLie stack, not a full non-Archimedean analysis library.

## Main definitions

* `IsInfinitesimal` — `|ε| < 1/n` for all positive naturals `n`
* `IsInfinite` — `n < |Ω|` for all naturals `n`
* `IsMacro` — bounded by some natural number

## Main results

* `isInfinitesimal_zero` — `0` is infinitesimal
* `IsInfinitesimal.neg` — closed under negation
-/

set_option autoImplicit false

namespace HeytingLean.SurrealLie

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]

/-! ### Infinitesimals -/

/-- `ε` is infinitesimal iff `|ε| < 1/n` for all positive naturals `n`. -/
def IsInfinitesimal (ε : 𝕜) : Prop :=
  ∀ n : ℕ, 0 < n → |ε| < (1 : 𝕜) / n

/-- Infinitesimals are closed under negation. -/
lemma IsInfinitesimal.neg {ε : 𝕜} (hε : IsInfinitesimal (𝕜 := 𝕜) ε) :
    IsInfinitesimal (𝕜 := 𝕜) (-ε) := by
  intro n hn
  simpa [abs_neg] using hε n hn

section Ordered

variable [IsStrictOrderedRing 𝕜]

/-- Zero is infinitesimal. -/
lemma isInfinitesimal_zero : IsInfinitesimal (𝕜 := 𝕜) (0 : 𝕜) := by
  intro n hn
  simp only [abs_zero]
  exact div_pos one_pos (Nat.cast_pos.mpr hn)

/-! ### Basic closure properties -/

/-- If `ε` is infinitesimal and `|a|` is bounded by a natural, then `a*ε` is infinitesimal. -/
lemma IsInfinitesimal.mul_of_abs_le {a ε : 𝕜} (hε : IsInfinitesimal (𝕜 := 𝕜) ε) {N : ℕ}
    (ha : |a| ≤ (N : 𝕜)) :
    IsInfinitesimal (𝕜 := 𝕜) (a * ε) := by
  intro n hn
  cases N with
  | zero =>
    have ha0 : |a| ≤ (0 : 𝕜) := by
      simpa using ha
    have habs : |a| = 0 := le_antisymm ha0 (abs_nonneg a)
    have a0 : a = 0 := (abs_eq_zero).1 habs
    have hz : IsInfinitesimal (𝕜 := 𝕜) (0 : 𝕜) := isInfinitesimal_zero (𝕜 := 𝕜)
    simpa [a0] using hz n hn
  | succ N =>
    have hn' : 0 < n * Nat.succ N := Nat.mul_pos hn (Nat.succ_pos _)
    have hε' := hε (n * Nat.succ N) hn'
    have hNpos : (0 : 𝕜) < (Nat.succ N : 𝕜) := Nat.cast_pos.mpr (Nat.succ_pos _)
    have habs_le : |a| * |ε| ≤ (Nat.succ N : 𝕜) * |ε| := by
      exact mul_le_mul_of_nonneg_right ha (abs_nonneg ε)
    have hε'' : |ε| < (1 : 𝕜) / ((n : 𝕜) * (Nat.succ N : 𝕜)) := by
      simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hε'
    have hlt :
        (Nat.succ N : 𝕜) * |ε| <
          (Nat.succ N : 𝕜) * ((1 : 𝕜) / ((n : 𝕜) * (Nat.succ N : 𝕜))) := by
      exact mul_lt_mul_of_pos_left hε'' hNpos
    calc
      |a * ε| = |a| * |ε| := by simp [abs_mul]
      _ < (Nat.succ N : 𝕜) * ((1 : 𝕜) / ((n : 𝕜) * (Nat.succ N : 𝕜))) :=
        lt_of_le_of_lt habs_le hlt
      _ = (1 : 𝕜) / n := by
        have hn0 : (n : 𝕜) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        have hN0 : (Nat.succ N : 𝕜) ≠ 0 := by
          exact_mod_cast (Nat.succ_ne_zero N)
        field_simp [hn0, hN0]

/-- Infinitesimals are closed under addition. -/
lemma IsInfinitesimal.add {ε δ : 𝕜}
    (hε : IsInfinitesimal (𝕜 := 𝕜) ε) (hδ : IsInfinitesimal (𝕜 := 𝕜) δ) :
    IsInfinitesimal (𝕜 := 𝕜) (ε + δ) := by
  intro n hn
  have hn2 : 0 < (2 * n) := Nat.mul_pos (by decide : 0 < 2) hn
  have hε' := hε (2 * n) hn2
  have hδ' := hδ (2 * n) hn2
  -- Triangle inequality plus halving the bound.
  have hsum : |ε + δ| ≤ |ε| + |δ| := abs_add_le _ _ 
  have hlt :
      |ε| + |δ| < (1 : 𝕜) / ((2 * n : ℕ) : 𝕜) + (1 : 𝕜) / ((2 * n : ℕ) : 𝕜) := by
    simpa using (add_lt_add hε' hδ')
  have hfrac : (1 : 𝕜) / ((2 * n : ℕ) : 𝕜) + (1 : 𝕜) / ((2 * n : ℕ) : 𝕜) = (1 : 𝕜) / n := by
    have hn0 : (n : 𝕜) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have h2n0 : ((2 * n : ℕ) : 𝕜) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn2)
    -- `a+a = 2*a`, then simplify `2/(2*n) = 1/n`.
    calc
      (1 : 𝕜) / ((2 * n : ℕ) : 𝕜) + (1 : 𝕜) / ((2 * n : ℕ) : 𝕜)
          = (2 : 𝕜) / ((2 * n : ℕ) : 𝕜) := by
              ring
      _ = (1 : 𝕜) / n := by
          have hprod0 : ( (2 : 𝕜) * (n : 𝕜) ) ≠ 0 := by
            simpa [Nat.cast_mul] using h2n0
          -- Rewrite the denominator as a product in `𝕜`, then clear denominators.
          -- `simp` here only rewrites casts; it does not change the inequality goal shape.
          have : (2 : 𝕜) / ((2 * n : ℕ) : 𝕜) = (2 : 𝕜) / ((2 : 𝕜) * (n : 𝕜)) := by
            simp [Nat.cast_mul]
          -- Now simplify `2 / (2*n) = 1/n`.
          -- (We keep `hn0` and `hprod0` to justify clearing denominators.)
          -- `field_simp` closes the ring identity.
          calc
            (2 : 𝕜) / ((2 * n : ℕ) : 𝕜) = (2 : 𝕜) / ((2 : 𝕜) * (n : 𝕜)) := this
            _ = (1 : 𝕜) / n := by
              field_simp [hn0, hprod0]
  exact lt_of_le_of_lt hsum (lt_of_lt_of_eq hlt hfrac)

end Ordered

/-! ### Infinite and macro predicates (definitions only) -/

/-- `Ω` is infinite iff `n < |Ω|` for all naturals `n`. -/
def IsInfinite (Ω : 𝕜) : Prop :=
  ∀ n : ℕ, (n : 𝕜) < |Ω|

/-- `a` is macro iff it is bounded by some natural number. -/
def IsMacro (a : 𝕜) : Prop :=
  ∃ N : ℕ, |a| ≤ (N : 𝕜)

end

end HeytingLean.SurrealLie
