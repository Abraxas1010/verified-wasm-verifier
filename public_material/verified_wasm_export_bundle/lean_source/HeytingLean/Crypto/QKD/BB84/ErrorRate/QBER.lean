import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import HeytingLean.Crypto.QKD.BB84.States

/-!
# Quantum Bit Error Rate (QBER)

This module defines a lightweight, purely finite notion of “error rate” for BB84:
given a finite sample of key-bit comparisons, count mismatches and normalize.

This is intentionally interface-first (no probability theory): it supports the
standard BB84 intercept-resend calculation and simple threshold checks.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84
namespace ErrorRate

noncomputable section

/-- A key-bit comparison result. -/
inductive BitComparison : Type
  | match_
  | mismatch
  deriving DecidableEq, Repr

/-- A sequence of `n` bit-comparisons (raw key check). -/
structure KeyComparison (n : ℕ) where
  results : Fin n → BitComparison

namespace KeyComparison

variable {n : ℕ} (kc : KeyComparison n)

/-- Count mismatches in a key comparison. -/
def errorCount : ℕ :=
  (Finset.univ.filter fun i => kc.results i = BitComparison.mismatch).card

theorem errorCount_le : kc.errorCount ≤ n := by
  classical
  -- `card (filter ...) ≤ card univ = n`.
  have h :=
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
      (p := fun i : Fin n => kc.results i = BitComparison.mismatch))
  simpa [KeyComparison.errorCount, Finset.card_univ] using h

/-- QBER as a real number: `errorCount / n`. -/
def qberReal : ℝ :=
  (kc.errorCount : ℝ) / n

theorem qber_bounds (hn : 0 < n) :
    0 ≤ kc.qberReal ∧ kc.qberReal ≤ 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : (kc.errorCount : ℝ) ≤ n := by exact_mod_cast kc.errorCount_le
    -- `a / n ≤ 1` since `a ≤ n` and `n > 0`.
    have : (kc.errorCount : ℝ) / n ≤ (1 : ℝ) := by
      have : (kc.errorCount : ℝ) ≤ (1 : ℝ) * n := by simpa using hle
      exact (div_le_iff₀ hn').2 this
    simpa [KeyComparison.qberReal] using this

/-- Perfect key: no mismatches. -/
def isPerfect : Prop :=
  kc.errorCount = 0

theorem qber_perfect (hPerf : kc.isPerfect) : kc.qberReal = 0 := by
  unfold KeyComparison.isPerfect at hPerf
  unfold KeyComparison.qberReal
  -- After rewriting the numerator to `0`, this is just `0 / n = 0`.
  simp [hPerf]

end KeyComparison

end

end ErrorRate
end BB84
end QKD
end Crypto
end HeytingLean
