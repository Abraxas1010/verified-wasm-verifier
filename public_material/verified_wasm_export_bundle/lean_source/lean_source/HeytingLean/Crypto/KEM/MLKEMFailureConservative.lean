import HeytingLean.Crypto.KEM.MLKEMFailureModel
import HeytingLean.Crypto.KEM.MLKEMMultiCoeffFailure
import HeytingLean.Crypto.KEM.MLKEMCompressBounds
import Mathlib.Algebra.Order.Field.Basic

/-!
# Conservative failure bounds (computed + proved; Gap 3)

This file provides **proved, computed** conservative bounds derived from the
`WindowedCounts` overflow upper bound (`sumOfCBDProducts_tailUB`).

Important: this is *not yet* the full ML-KEM decryption-failure probability.
It is a conservative, computed bound for the simplified “iid sum-of-products” model currently
implemented in `MLKEMFailureModel.lean`.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open FailureModel
open MultiCoeff

namespace ConservativeBounds

/-- Total random bits used by `terms` independent pairs of CBD samples. -/
def expBits (etaA etaB terms : Nat) : Nat :=
  terms * (2 * etaA + 2 * etaB)

/-- Total number of outcomes for `terms` pairs of CBD samples. -/
def totalOutcomes (etaA etaB terms : Nat) : Nat :=
  2 ^ expBits etaA etaB terms

/-- A computed upper bound on the tail numerator for one coefficient (count). -/
def singleCoeffTailUBCount (p : MLKEM203Params) (terms threshold : Nat) : Nat :=
  sumOfCBDProducts_tailUB p.eta1 p.eta2 terms threshold

/-- “Union bound is ≤ 2^-k”: cross-multiplied in `Nat` (no rationals). -/
def unionBoundOk (p : MLKEM203Params) (terms threshold k : Nat) : Prop :=
  singleCoeffTailUBCount p terms threshold * p.n * 2 ^ k ≤ totalOutcomes p.eta1 p.eta2 terms

instance (p : MLKEM203Params) (terms threshold k : Nat) : Decidable (unionBoundOk p terms threshold k) := by
  unfold unionBoundOk
  infer_instance

/-- Conservative computed proxy for `failureProbability` (still a *model*, not validated). -/
noncomputable def failureProbabilityComputed (p : MLKEM203Params) (terms threshold : Nat) : ℚ :=
  let num : ℚ := (singleCoeffTailUBCount p terms threshold : ℚ) * (p.n : ℚ)
  let den : ℚ := (totalOutcomes p.eta1 p.eta2 terms : ℚ)
  num / den

theorem failureProbabilityComputed_le_of_unionBoundOk
    (p : MLKEM203Params) (terms threshold k : Nat)
    (hok : unionBoundOk p terms threshold k) :
    failureProbabilityComputed p terms threshold ≤ (1 : ℚ) / ((2 : ℚ) ^ k) := by
  classical
  have hdenPosNat : 0 < totalOutcomes p.eta1 p.eta2 terms :=
    by
      dsimp [totalOutcomes]
      exact Nat.pow_pos (by decide : 0 < 2)
  have hdenPos : (0 : ℚ) < (totalOutcomes p.eta1 p.eta2 terms : ℚ) := by
    exact_mod_cast hdenPosNat
  have hkPos : (0 : ℚ) < (2 : ℚ) ^ k := by
    exact pow_pos (by norm_num) _

  -- Cast the `Nat` inequality into `ℚ` and normalize it to `num * 2^k ≤ den`.
  have hokQ :
      ((singleCoeffTailUBCount p terms threshold * p.n * 2 ^ k : Nat) : ℚ) ≤
        (totalOutcomes p.eta1 p.eta2 terms : ℚ) := by
    exact_mod_cast hok
  have hmulQ :
      ((singleCoeffTailUBCount p terms threshold : ℚ) * (p.n : ℚ)) * ((2 : ℚ) ^ k) ≤
        (totalOutcomes p.eta1 p.eta2 terms : ℚ) := by
    simpa [singleCoeffTailUBCount, totalOutcomes, expBits, mul_assoc, mul_left_comm, mul_comm] using hokQ

  let numQ : ℚ := (singleCoeffTailUBCount p terms threshold : ℚ) * (p.n : ℚ)
  let denQ : ℚ := (totalOutcomes p.eta1 p.eta2 terms : ℚ)
  have hmulQ' : numQ * ((2 : ℚ) ^ k) ≤ denQ := by
    simpa [numQ, denQ, mul_assoc, mul_left_comm, mul_comm] using hmulQ
  have hnumLe : numQ ≤ denQ / ((2 : ℚ) ^ k) := by
    exact (le_div_iff₀ hkPos).2 (by simpa [mul_assoc] using hmulQ')
  have hdivLe : numQ / denQ ≤ (1 : ℚ) / ((2 : ℚ) ^ k) := by
    refine (div_le_iff₀ hdenPos).2 ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnumLe
  simpa [failureProbabilityComputed, numQ, denQ] using hdivLe

/-!
## Concrete proved bounds (full ML-KEM scales, ≤ 60s on the dev box)

These are chosen to be strong-but-realistic: they aim for the “provable in Lean” conservative
targets (`2^-80`, `2^-95`) rather than the NIST heuristic exponents.
-/

def thresholdQ4 : Nat := 3329 / 4
def adjustedThreshold (Acomp : Nat) : Nat := thresholdQ4 - Acomp

theorem mlkem512_unionBoundOk_80 :
    unionBoundOk mlkem512 (mlkem512.k * mlkem512.n) thresholdQ4 80 := by
  native_decide

theorem mlkem768_unionBoundOk_80 :
    unionBoundOk mlkem768 (mlkem768.k * mlkem768.n) thresholdQ4 80 := by
  native_decide

theorem mlkem1024_unionBoundOk_95 :
    unionBoundOk mlkem1024 (mlkem1024.k * mlkem1024.n) thresholdQ4 95 := by
  native_decide

theorem mlkem512_failureProbabilityComputed_le_2pow_neg_80 :
    failureProbabilityComputed mlkem512 (mlkem512.k * mlkem512.n) thresholdQ4 ≤ (1 : ℚ) / ((2 : ℚ) ^ 80) := by
  exact failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem512_unionBoundOk_80

theorem mlkem768_failureProbabilityComputed_le_2pow_neg_80 :
    failureProbabilityComputed mlkem768 (mlkem768.k * mlkem768.n) thresholdQ4 ≤ (1 : ℚ) / ((2 : ℚ) ^ 80) := by
  exact failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem768_unionBoundOk_80

theorem mlkem1024_failureProbabilityComputed_le_2pow_neg_95 :
    failureProbabilityComputed mlkem1024 (mlkem1024.k * mlkem1024.n) thresholdQ4 ≤ (1 : ℚ) / ((2 : ℚ) ^ 95) := by
  exact failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem1024_unionBoundOk_95

/-!
## NIST-exponent bounds for the current computed model

These show that the *computed proxy bound* also satisfies the published NIST exponents (and in fact
much stronger ones). This still does **not** replace the NIST axioms about the real ML-KEM
implementation, but it provides the missing computational evidence under an explicit model.
-/

open HeytingLean.Crypto.KEM.FIPS203

private theorem twoNeg_succ_lt (e : Nat) : twoNeg (e + 1) < twoNeg e := by
  have hpos : (0 : ℚ) < twoNeg e := by
    simp [twoNeg]
  have hstep : twoNeg (e + 1) = twoNeg e / 2 := by
    simp [twoNeg, pow_succ, div_mul_eq_div_div]
  have hlt : twoNeg e / 2 < twoNeg e := by
    exact div_lt_self hpos (by norm_num : (1 : ℚ) < (2 : ℚ))
  simpa [hstep] using hlt

private def nistK (p : MLKEM203Params) : Nat :=
  reportedFailureExponent p

theorem mlkem512_unionBoundOk_nistPlus1 :
    unionBoundOk mlkem512 (mlkem512.k * mlkem512.n) thresholdQ4 (nistK mlkem512 + 1) := by
  native_decide

theorem mlkem768_unionBoundOk_nistPlus1 :
    unionBoundOk mlkem768 (mlkem768.k * mlkem768.n) thresholdQ4 (nistK mlkem768 + 1) := by
  native_decide

theorem mlkem1024_unionBoundOk_nistPlus1 :
    unionBoundOk mlkem1024 (mlkem1024.k * mlkem1024.n) thresholdQ4 (nistK mlkem1024 + 1) := by
  native_decide

theorem mlkem512_failureProbabilityComputed_lt_reportedFailureBoundQ :
    failureProbabilityComputed mlkem512 (mlkem512.k * mlkem512.n) thresholdQ4 < reportedFailureBoundQ mlkem512 := by
  have hle :
      failureProbabilityComputed mlkem512 (mlkem512.k * mlkem512.n) thresholdQ4 ≤ twoNeg (nistK mlkem512 + 1) :=
    (failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem512_unionBoundOk_nistPlus1)
  have hlt : twoNeg (nistK mlkem512 + 1) < twoNeg (nistK mlkem512) := twoNeg_succ_lt _
  have : twoNeg (nistK mlkem512) = reportedFailureBoundQ mlkem512 := by
    simp [reportedFailureBoundQ, nistK]
  exact lt_of_le_of_lt hle (by simpa [this] using hlt)

theorem mlkem768_failureProbabilityComputed_lt_reportedFailureBoundQ :
    failureProbabilityComputed mlkem768 (mlkem768.k * mlkem768.n) thresholdQ4 < reportedFailureBoundQ mlkem768 := by
  have hle :
      failureProbabilityComputed mlkem768 (mlkem768.k * mlkem768.n) thresholdQ4 ≤ twoNeg (nistK mlkem768 + 1) :=
    (failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem768_unionBoundOk_nistPlus1)
  have hlt : twoNeg (nistK mlkem768 + 1) < twoNeg (nistK mlkem768) := twoNeg_succ_lt _
  have : twoNeg (nistK mlkem768) = reportedFailureBoundQ mlkem768 := by
    simp [reportedFailureBoundQ, nistK]
  exact lt_of_le_of_lt hle (by simpa [this] using hlt)

theorem mlkem1024_failureProbabilityComputed_lt_reportedFailureBoundQ :
    failureProbabilityComputed mlkem1024 (mlkem1024.k * mlkem1024.n) thresholdQ4 < reportedFailureBoundQ mlkem1024 := by
  have hle :
      failureProbabilityComputed mlkem1024 (mlkem1024.k * mlkem1024.n) thresholdQ4 ≤ twoNeg (nistK mlkem1024 + 1) :=
    (failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem1024_unionBoundOk_nistPlus1)
  have hlt : twoNeg (nistK mlkem1024 + 1) < twoNeg (nistK mlkem1024) := twoNeg_succ_lt _
  have : twoNeg (nistK mlkem1024) = reportedFailureBoundQ mlkem1024 := by
    simp [reportedFailureBoundQ, nistK]
  exact lt_of_le_of_lt hle (by simpa [this] using hlt)

/-!
## Compression-adjusted computed bounds (proxy)

We reduce the coefficient threshold by the per-coefficient compression bound from
`MLKEMCompressBounds`. This provides a concrete, compression-aware computed proxy bound
for use the explicit model-bridge assumption in `MLKEMFailureModelBridge`.
-/

open HeytingLean.Crypto.KEM.FIPS203.CompressBounds
open HeytingLean.Crypto.KEM.FIPS203.Compress

def Acomp512 : Nat := 105
def Acomp768 : Nat := 105
def Acomp1024 : Nat := 53

theorem compressionError_dv4_le_Acomp512 (x : ZMod 3329) :
    compressionError (q := 3329) (d := 4) x ≤ Acomp512 := by
  simpa [Acomp512] using (compressionError_dv4_le105 (x := x))

theorem compressionError_dv5_le_Acomp1024 (x : ZMod 3329) :
    compressionError (q := 3329) (d := 5) x ≤ Acomp1024 := by
  simpa [Acomp1024] using (compressionError_dv5_le53 (x := x))

theorem mlkem512_unionBoundOk_nistPlus1_with_compression :
    unionBoundOk mlkem512 (mlkem512.k * mlkem512.n) (adjustedThreshold Acomp512) (nistK mlkem512 + 1) := by
  native_decide

theorem mlkem768_unionBoundOk_nistPlus1_with_compression :
    unionBoundOk mlkem768 (mlkem768.k * mlkem768.n) (adjustedThreshold Acomp768) (nistK mlkem768 + 1) := by
  native_decide

theorem mlkem1024_unionBoundOk_nistPlus1_with_compression :
    unionBoundOk mlkem1024 (mlkem1024.k * mlkem1024.n) (adjustedThreshold Acomp1024) (nistK mlkem1024 + 1) := by
  native_decide

theorem mlkem512_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ :
    failureProbabilityComputed mlkem512 (mlkem512.k * mlkem512.n) (adjustedThreshold Acomp512) <
      reportedFailureBoundQ mlkem512 := by
  have hle :
      failureProbabilityComputed mlkem512 (mlkem512.k * mlkem512.n) (adjustedThreshold Acomp512) ≤
        twoNeg (nistK mlkem512 + 1) :=
    failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem512_unionBoundOk_nistPlus1_with_compression
  have hlt : twoNeg (nistK mlkem512 + 1) < twoNeg (nistK mlkem512) := twoNeg_succ_lt _
  have : twoNeg (nistK mlkem512) = reportedFailureBoundQ mlkem512 := by
    simp [reportedFailureBoundQ, nistK]
  exact lt_of_le_of_lt hle (by simpa [this] using hlt)

theorem mlkem768_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ :
    failureProbabilityComputed mlkem768 (mlkem768.k * mlkem768.n) (adjustedThreshold Acomp768) <
      reportedFailureBoundQ mlkem768 := by
  have hle :
      failureProbabilityComputed mlkem768 (mlkem768.k * mlkem768.n) (adjustedThreshold Acomp768) ≤
        twoNeg (nistK mlkem768 + 1) :=
    failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem768_unionBoundOk_nistPlus1_with_compression
  have hlt : twoNeg (nistK mlkem768 + 1) < twoNeg (nistK mlkem768) := twoNeg_succ_lt _
  have : twoNeg (nistK mlkem768) = reportedFailureBoundQ mlkem768 := by
    simp [reportedFailureBoundQ, nistK]
  exact lt_of_le_of_lt hle (by simpa [this] using hlt)

theorem mlkem1024_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ :
    failureProbabilityComputed mlkem1024 (mlkem1024.k * mlkem1024.n) (adjustedThreshold Acomp1024) <
      reportedFailureBoundQ mlkem1024 := by
  have hle :
      failureProbabilityComputed mlkem1024 (mlkem1024.k * mlkem1024.n) (adjustedThreshold Acomp1024) ≤
        twoNeg (nistK mlkem1024 + 1) :=
    failureProbabilityComputed_le_of_unionBoundOk _ _ _ _ mlkem1024_unionBoundOk_nistPlus1_with_compression
  have hlt : twoNeg (nistK mlkem1024 + 1) < twoNeg (nistK mlkem1024) := twoNeg_succ_lt _
  have : twoNeg (nistK mlkem1024) = reportedFailureBoundQ mlkem1024 := by
    simp [reportedFailureBoundQ, nistK]
  exact lt_of_le_of_lt hle (by simpa [this] using hlt)

theorem mlkem512_singleCoeffTailUBQ_with_compression_ge :
    singleCoeffTailUBQ mlkem512.eta1 mlkem512.eta2 (mlkem512.k * mlkem512.n) thresholdQ4 ≤
      singleCoeffTailUBQ mlkem512.eta1 mlkem512.eta2 (mlkem512.k * mlkem512.n) (adjustedThreshold Acomp512) := by
  apply singleCoeffTailUBQ_mono_threshold
  native_decide

theorem mlkem768_singleCoeffTailUBQ_with_compression_ge :
    singleCoeffTailUBQ mlkem768.eta1 mlkem768.eta2 (mlkem768.k * mlkem768.n) thresholdQ4 ≤
      singleCoeffTailUBQ mlkem768.eta1 mlkem768.eta2 (mlkem768.k * mlkem768.n) (adjustedThreshold Acomp768) := by
  apply singleCoeffTailUBQ_mono_threshold
  native_decide

theorem mlkem1024_singleCoeffTailUBQ_with_compression_ge :
    singleCoeffTailUBQ mlkem1024.eta1 mlkem1024.eta2 (mlkem1024.k * mlkem1024.n) thresholdQ4 ≤
      singleCoeffTailUBQ mlkem1024.eta1 mlkem1024.eta2 (mlkem1024.k * mlkem1024.n) (adjustedThreshold Acomp1024) := by
  apply singleCoeffTailUBQ_mono_threshold
  native_decide

end ConservativeBounds

end FIPS203
end KEM
end Crypto
end HeytingLean
