import Mathlib.Data.Real.Basic
import HeytingLean.Crypto.Information.PrivacyAmplification
import HeytingLean.Crypto.QKD.BB84.ErrorRate
import HeytingLean.Crypto.SecurityBounds

/-!
# BB84 probabilistic/finite-key security (interface-first)

This layer is intentionally lightweight:
- it reuses the existing QBER development (`BB84.ErrorRate`);
- it packages finite-key bookkeeping (`FiniteKeyBound`);
- it leaves concrete secrecy bounds (entropy, leftover hash lemma) as future work.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Crypto.Information.Hashing
open HeytingLean.Crypto.Information.PrivacyAmplification
open HeytingLean.Crypto.SecurityBounds

/-- A BB84 finite-key security statement packaged with a bookkeeping bound. -/
structure BB84FiniteKeySecurity where
  bound : FiniteKeyBound
  /-- Observed QBER (e.g. from `KeyComparison.qberReal`). -/
  observedQBER : ℝ
  observedQBER_nonneg : 0 ≤ observedQBER

/-- The total ε associated to a BB84 finite-key security record. -/
def BB84FiniteKeySecurity.epsilonTotal (S : BB84FiniteKeySecurity) : ℝ :=
  S.bound.epsilon_total

/-- A BB84 finite-key record covers an extraction error when it fits inside `epsilon_sec`. -/
def BB84FiniteKeySecurity.coversExtractionError (S : BB84FiniteKeySecurity) (ε : ℝ) : Prop :=
  ε ≤ S.bound.epsilon_sec

/-- Convenience wrapper around `coversExtractionError` for a public-seed extraction witness. -/
def BB84FiniteKeySecurity.coversExtractionWitness {D R Seed : Type*}
    [Fintype D] [Fintype R] [Fintype Seed] [DecidableEq R] [TwoUniversal D R Seed]
    (S : BB84FiniteKeySecurity) (W : PublicSeededExtractionWitness D R Seed) : Prop :=
  S.coversExtractionError W.extractionError

/-- If the secrecy budget covers the extraction witness, the actual output is within `epsilon_sec`. -/
theorem BB84FiniteKeySecurity.statDistance_le_epsilonSec {D R Seed : Type*}
    [Fintype D] [Fintype R] [Fintype Seed] [DecidableEq R] [TwoUniversal D R Seed]
    (S : BB84FiniteKeySecurity) (W : PublicSeededExtractionWitness D R Seed)
    (hcover : S.coversExtractionWitness W) :
    Finite.statDistance W.actualDist W.idealDist ≤ S.bound.epsilon_sec := by
  exact le_trans W.statDistance_le_extractionError hcover

/-- The total finite-key budget covers correctness plus any covered extraction error. -/
theorem BB84FiniteKeySecurity.correctness_plus_extraction_le_total
    (S : BB84FiniteKeySecurity) {ε : ℝ} (hε : S.coversExtractionError ε) :
    S.bound.epsilon_cor + ε ≤ S.epsilonTotal := by
  dsimp [BB84FiniteKeySecurity.coversExtractionError, BB84FiniteKeySecurity.epsilonTotal,
    FiniteKeyBound.epsilon_total] at *
  exact add_le_add_left hε _

end BB84
end QKD
end Crypto
end HeytingLean
