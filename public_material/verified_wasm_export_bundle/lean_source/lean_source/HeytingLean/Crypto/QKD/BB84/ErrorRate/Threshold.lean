import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import HeytingLean.Crypto.QKD.BB84.ErrorRate.InterceptResend

/-!
# BB84 QBER thresholds

This module records common “abort thresholds” for BB84 in terms of QBER.
We then show the standard intercept-resend rate implies detection above the
conservative 11% threshold once Eve intercepts more than 44% of qubits.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84
namespace ErrorRate

noncomputable section

/-- Conservative security threshold (11%). -/
def conservativeThreshold : ℝ := (11 : ℝ) / 100

/-- Theoretical limit (~14.6%): `1 - 1/√2`. -/
noncomputable def theoreticalThreshold : ℝ := 1 - 1 / Real.sqrt 2

/-- Default threshold used here: the conservative one. -/
def securityThreshold : ℝ := conservativeThreshold

/-- A QBER value is “secure” if below threshold. -/
def isSecureQBER (q : ℝ) : Prop :=
  q < securityThreshold

/-- A QBER value indicates likely eavesdropping if at/above threshold. -/
def indicatesEavesdropping (q : ℝ) : Prop :=
  q ≥ securityThreshold

theorem full_interception_detected :
    indicatesEavesdropping (expectedQBER fullInterception) := by
  simp [indicatesEavesdropping, securityThreshold, conservativeThreshold, full_interception_qber]
  norm_num

/-- If Eve intercepts more than 44% of qubits, the expected QBER exceeds 11%. -/
theorem interception_detectable (p : InterceptionRate)
    (h : p.rate > (44 : ℝ) / 100) :
    indicatesEavesdropping (expectedQBER p) := by
  have h' : p.rate / 4 > (11 : ℝ) / 100 := by
    -- Since `44/100 / 4 = 11/100`.
    linarith
  have : expectedQBER p ≥ securityThreshold := by
    -- Convert strict bound to `≥` and rewrite.
    have : expectedQBER p > securityThreshold := by
      simpa [securityThreshold, conservativeThreshold, expectedQBER_eq_rate_div_4] using h'
    exact le_of_lt this
  exact this

theorem secure_implies_limited_interception (p : InterceptionRate)
    (hSec : isSecureQBER (expectedQBER p)) :
    p.rate < (44 : ℝ) / 100 := by
  -- `expectedQBER p = p/4 < 11/100` implies `p < 44/100`.
  have : p.rate / 4 < (11 : ℝ) / 100 := by
    simpa [isSecureQBER, securityThreshold, conservativeThreshold, expectedQBER_eq_rate_div_4] using hSec
  linarith

/-- Security margin: how much QBER can come from channel noise while still detecting Eve at rate `p`. -/
def securityMargin (p : InterceptionRate) : ℝ :=
  securityThreshold - expectedQBER p

theorem full_margin_no_interception :
    securityMargin noInterception = securityThreshold := by
  simp [securityMargin, no_interception_qber]

end

end ErrorRate
end BB84
end QKD
end Crypto
end HeytingLean
