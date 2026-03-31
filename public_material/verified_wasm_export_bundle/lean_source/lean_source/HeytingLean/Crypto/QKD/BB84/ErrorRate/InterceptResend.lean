import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Crypto.QKD.BB84.ErrorRate.QBER

/-!
# Intercept-resend: expected QBER

This module encodes the standard BB84 intercept-resend calculation:

- Eve intercepts with probability `p`
- Eve’s basis guess is correct with probability 1/2 and wrong with probability 1/2
- If Eve uses the wrong basis, Bob’s bit flips with probability 1/2 (conditioned on sifting)

Thus: `QBER = p * (1/2) * (1/2) = p / 4`.

We keep everything as simple real arithmetic (no probability theory).
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84
namespace ErrorRate

noncomputable section

/-- Eve's interception rate `p ∈ [0,1]`. -/
structure InterceptionRate where
  rate : ℝ
  nonneg : 0 ≤ rate
  le_one : rate ≤ 1

/-- Probability Eve chooses the wrong basis (uniform choice). -/
def probWrongBasis : ℝ := (1 : ℝ) / 2

/-- Probability Bob's bit is wrong given Eve used the wrong basis. -/
def probErrorGivenWrongBasis : ℝ := (1 : ℝ) / 2

/-- Expected QBER from an intercept-resend attack. -/
def expectedQBER (p : InterceptionRate) : ℝ :=
  p.rate * probWrongBasis * probErrorGivenWrongBasis

theorem expectedQBER_eq_rate_div_4 (p : InterceptionRate) :
    expectedQBER p = p.rate / 4 := by
  simp [expectedQBER, probWrongBasis, probErrorGivenWrongBasis]
  ring

/-- Full interception (`p = 1`). -/
def fullInterception : InterceptionRate :=
  ⟨1, by norm_num, by norm_num⟩

theorem full_interception_qber : expectedQBER fullInterception = (1 : ℝ) / 4 := by
  simp [expectedQBER, fullInterception, probWrongBasis, probErrorGivenWrongBasis]
  ring

/-- No interception (`p = 0`). -/
def noInterception : InterceptionRate :=
  ⟨0, by norm_num, by norm_num⟩

theorem no_interception_qber : expectedQBER noInterception = 0 := by
  simp [expectedQBER, noInterception, probWrongBasis, probErrorGivenWrongBasis]

/-- Expected QBER is monotone in the interception rate. -/
theorem qber_monotone (p q : InterceptionRate) (h : p.rate ≤ q.rate) :
    expectedQBER p ≤ expectedQBER q := by
  have h1 : 0 ≤ probWrongBasis := by norm_num [probWrongBasis]
  have h2 : 0 ≤ probErrorGivenWrongBasis := by norm_num [probErrorGivenWrongBasis]
  -- Multiply the inequality `p.rate ≤ q.rate` by nonnegative factors.
  have : p.rate * probWrongBasis ≤ q.rate * probWrongBasis :=
    mul_le_mul_of_nonneg_right h h1
  have : p.rate * probWrongBasis * probErrorGivenWrongBasis ≤
      q.rate * probWrongBasis * probErrorGivenWrongBasis :=
    mul_le_mul_of_nonneg_right this h2
  simpa [expectedQBER, mul_assoc] using this

end

end ErrorRate
end BB84
end QKD
end Crypto
end HeytingLean
