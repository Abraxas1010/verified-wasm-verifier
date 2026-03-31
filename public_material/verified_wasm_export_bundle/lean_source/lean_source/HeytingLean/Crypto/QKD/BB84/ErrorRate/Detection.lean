import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Crypto.QKD.BB84.ErrorRate.Threshold

/-!
# Statistical detection (interface-first)

This module provides a small *interface-first* layer for statistical detection
around QBER estimation. We do **not** formalize the probability theory behind
Hoeffding-style concentration bounds here; instead we record the standard
closed-form bound as a function and prove basic algebraic properties about it.

Downstream protocol analyses can *use* these bounds once a concrete probability
model is chosen.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84
namespace ErrorRate

noncomputable section

/-- Number of test bits used for QBER estimation. -/
structure TestSampleSize where
  n : ℕ
  pos : 0 < n

/-- Hoeffding-style upper bound `2 * exp(-2 n ε^2)` (recorded as a function). -/
def hoeffdingBound (sample : TestSampleSize) (epsilon : ℝ) : ℝ :=
  2 * Real.exp (-2 * (sample.n : ℝ) * epsilon ^ 2)

theorem hoeffdingBound_nonneg (sample : TestSampleSize) (epsilon : ℝ) :
    0 ≤ hoeffdingBound sample epsilon := by
  refine mul_nonneg (by norm_num) ?_
  exact (Real.exp_pos _).le

theorem hoeffdingBound_lt_two_of_ne_zero (sample : TestSampleSize) {epsilon : ℝ}
    (hε : epsilon ≠ 0) :
    hoeffdingBound sample epsilon < 2 := by
  have hn : (0 : ℝ) < (sample.n : ℝ) := by exact_mod_cast sample.pos
  have hεsq : (0 : ℝ) < epsilon ^ 2 :=
    sq_pos_of_ne_zero hε
  have harg : (-2 * (sample.n : ℝ) * epsilon ^ 2) < 0 := by
    nlinarith [hn, hεsq]
  have hexp : Real.exp (-2 * (sample.n : ℝ) * epsilon ^ 2) < 1 := by
    -- `exp x < 1` iff `x < 0`.
    simpa [Real.exp_lt_one_iff] using harg
  have hpos : (0 : ℝ) < 2 := by norm_num
  have : 2 * Real.exp (-2 * (sample.n : ℝ) * epsilon ^ 2) < 2 * (1 : ℝ) :=
    mul_lt_mul_of_pos_left hexp hpos
  simpa [hoeffdingBound] using this

/-- Convenience sample size: 300 test bits. -/
def sample300 : TestSampleSize := ⟨300, by norm_num⟩

/-- A small record packaging false-positive/false-negative rates. -/
structure DetectionAccuracy where
  falsePositiveRate : ℝ
  falseNegativeRate : ℝ
  fpr_nonneg : 0 ≤ falsePositiveRate
  fnr_nonneg : 0 ≤ falseNegativeRate

end

end ErrorRate
end BB84
end QKD
end Crypto
end HeytingLean
