import Mathlib.Tactic
import HeytingLean.Crypto.ConstructiveHardness.Security
import HeytingLean.Crypto.QKD.E91.Eavesdropping
import HeytingLean.Crypto.QKD.E91.Protocol
import HeytingLean.Crypto.Quantum.Bell.CHSH.CHSHInequality
import HeytingLean.Crypto.Quantum.Bell.Tsirelson.Achievability

/-!
# E91 security layers

This file contains two complementary, interface-first layers:

* **Constructor-Theoretic (CT)**: apply the project’s generic
  “no-cloning ⇒ eavesdropping-impossible” theorem to the toy E91 superinformation medium.
  (`e91_secure`, `intercept_impossible`)
* **Device-Independent (DI, LHV model)**: CHSH violation rules out all local hidden variable
  explanations for an observed transcript. (`InLHVSet`, `e91_secure_di`)
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

/-!
## DI: CHSH violation ⇒ no LHV explanation
-/

open HeytingLean.Crypto.Quantum.Bell.CHSH

/-- A correlator is *LHV-realizable* if it comes from some finite local hidden variable model. -/
def InLHVSet (C : Correlator) : Prop :=
  ∃ M : LocalHiddenVariableModel, M.toCorrelator = C

theorem chsh_abs_le_two_of_inLHV {C : Correlator} (h : InLHVSet C) :
    |chshQuantity C| ≤ (2 : ℝ) := by
  rcases h with ⟨M, rfl⟩
  simpa using (LocalHiddenVariableModel.chsh_inequality (M := M))

/-- If `|S| > 2`, the correlator cannot be explained by any LHV model. -/
theorem no_lhv_of_chsh_violation {C : Correlator} (h : (2 : ℝ) < |chshQuantity C|) :
    ¬ InLHVSet C := by
  intro hLHV
  exact (not_lt_of_ge (chsh_abs_le_two_of_inLHV hLHV) h)

/-- DI-style E91 security statement: CHSH violation rules out LHV explanations. -/
theorem e91_secure_di (T : Transcript) (h : (2 : ℝ) < |T.score|) :
    ¬ InLHVSet T.correlator := by
  have : (2 : ℝ) < |chshQuantity T.correlator| := by
    simpa [Transcript.score] using h
  exact no_lhv_of_chsh_violation this

namespace Examples

open HeytingLean.Crypto.Quantum.Bell.Tsirelson
open HeytingLean.Crypto.Quantum.Bell.Tsirelson.Examples

noncomputable section

/-- An explicit transcript achieving the Tsirelson score `S = 2√2`. -/
def tsirelsonTranscript : Transcript :=
  { correlator := tsirelsonAchievingStrategy.toCorrelator }

theorem tsirelsonTranscript_score :
    tsirelsonTranscript.score = 2 * Real.sqrt 2 := by
  simpa [tsirelsonTranscript, Transcript.score] using
    (achieves_tsirelson)

theorem tsirelsonTranscript_violates_lhv :
    (2 : ℝ) < |tsirelsonTranscript.score| := by
  have hs : tsirelsonTranscript.score = 2 * Real.sqrt 2 := tsirelsonTranscript_score
  have hpos : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by
    have : (0 : ℝ) ≤ Real.sqrt 2 := le_of_lt (Real.sqrt_pos.2 (by norm_num))
    nlinarith
  have habs : |tsirelsonTranscript.score| = 2 * Real.sqrt 2 := by
    simp [hs, abs_of_nonneg hpos]
  have hone : (1 : ℝ) < Real.sqrt 2 := by simpa using Real.one_lt_sqrt_two
  have hgt : (2 : ℝ) < 2 * Real.sqrt 2 := by nlinarith [hone]
  simpa [habs] using hgt

theorem tsirelsonTranscript_not_lhv :
    ¬ InLHVSet tsirelsonTranscript.correlator := by
  have h : (2 : ℝ) < |chshQuantity tsirelsonTranscript.correlator| := by
    simpa [tsirelsonTranscript, Transcript.score] using tsirelsonTranscript_violates_lhv
  exact no_lhv_of_chsh_violation h

end

end Examples

/-!
## CT: no-cloning ⇒ eavesdropping-impossible
-/

open HeytingLean.Constructor.CT
open HeytingLean.Crypto.ConstructiveHardness

theorem e91_secure : SecureAgainstEavesdropping E91Substrate e91TaskCT e91Superinfo :=
  superinfo_secure_against_eavesdropping e91TaskCT e91Superinfo

theorem intercept_impossible :
    e91TaskCT.impossible interceptStrategy.intercept := by
  have hsec : SecureAgainstEavesdropping E91Substrate e91TaskCT e91Superinfo := e91_secure
  refine hsec interceptStrategy ?_
  intro hPossible
  simpa [e91Superinfo] using (intercept_requires_copyAll hPossible)

end E91
end QKD
end Crypto
end HeytingLean
