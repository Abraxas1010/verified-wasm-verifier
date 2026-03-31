import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMFailureModel

/-!
# ML-KEM multi-coefficient failure aggregation (union bound shell)

ML-KEM decryption failure happens if **any** coefficient exceeds the decoding threshold.

This module records conservative *aggregation* logic (union bound style) without committing to a
specific probability model:

- given an upper bound `δ₁` for a single coefficient failing, a conservative upper bound for
  any of `n` coefficients failing is `n * δ₁`.

This is a bridge layer between:
- per-coefficient tail bounds (computed via `WindowedCounts` in Gap 3 work), and
- the global failure probability quantity recorded in `MLKEMAxioms.lean`.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators

namespace MultiCoeff

/-- Conservative union-bound aggregation. -/
noncomputable def unionBoundQ (n : Nat) (δ₁ : ℚ) : ℚ :=
  (n : ℚ) * δ₁

theorem unionBoundQ_mono_left {n₁ n₂ : Nat} (h : n₁ ≤ n₂) (δ₁ : ℚ) (hδ : 0 ≤ δ₁) :
    unionBoundQ n₁ δ₁ ≤ unionBoundQ n₂ δ₁ := by
  have : (n₁ : ℚ) ≤ (n₂ : ℚ) := by exact_mod_cast h
  simpa [unionBoundQ] using mul_le_mul_of_nonneg_right this hδ

/-- Per-parameter-set aggregation: `n=256` for ML-KEM. -/
noncomputable def mlkemUnionBound (p : MLKEM203Params) (δ₁ : ℚ) : ℚ :=
  unionBoundQ p.n δ₁

/-!
## Compression-adjusted aggregation helper

If per-coefficient compression noise is bounded by `Acomp`, then a sufficient condition for
`|residual + compression| ≤ T` is `|residual| ≤ T - Acomp`. We expose a concrete bound that
feeds a compression-adjusted threshold into the single-coefficient tail estimate and then
applies the union bound over `n` coefficients.
-/

def expBits (etaA etaB terms : Nat) : Nat :=
  terms * (2 * etaA + 2 * etaB)

noncomputable def singleCoeffTailUBQ (etaA etaB terms threshold : Nat) : ℚ :=
  let num : ℚ := (FailureModel.sumOfCBDProducts_tailUB etaA etaB terms threshold : ℚ)
  let den : ℚ := (2 : ℚ) ^ expBits etaA etaB terms
  num / den

noncomputable def multiCoeffTailUBQ (p : MLKEM203Params) (terms threshold : Nat) : ℚ :=
  mlkemUnionBound p (singleCoeffTailUBQ p.eta1 p.eta2 terms threshold)

noncomputable def multiCoeffTailUBQ_with_compression (p : MLKEM203Params)
    (terms threshold Acomp : Nat) : ℚ :=
  multiCoeffTailUBQ p terms (threshold - Acomp)

theorem multiCoeffTailUBQ_with_compression_eq (p : MLKEM203Params)
    (terms threshold Acomp : Nat) :
    multiCoeffTailUBQ_with_compression p terms threshold Acomp =
      mlkemUnionBound p (singleCoeffTailUBQ p.eta1 p.eta2 terms (threshold - Acomp)) := by
  rfl

theorem singleCoeffTailUBQ_mono_threshold
    (etaA etaB terms : Nat) {t₁ t₂ : Nat}
    (h : FailureModel.sumOfCBDProducts_tailUB etaA etaB terms t₂ ≤
      FailureModel.sumOfCBDProducts_tailUB etaA etaB terms t₁) :
    singleCoeffTailUBQ etaA etaB terms t₂ ≤ singleCoeffTailUBQ etaA etaB terms t₁ := by
  classical
  have hq :
      ((FailureModel.sumOfCBDProducts_tailUB etaA etaB terms t₂ : Nat) : ℚ) ≤
        (FailureModel.sumOfCBDProducts_tailUB etaA etaB terms t₁ : ℚ) := by
    exact_mod_cast h
  have hdenPos : 0 ≤ (2 : ℚ) ^ expBits etaA etaB terms := by
    exact le_of_lt (pow_pos (by norm_num) _)
  -- Divide by the same positive denominator.
  have hdiv : ((FailureModel.sumOfCBDProducts_tailUB etaA etaB terms t₂ : ℚ) /
        (2 : ℚ) ^ expBits etaA etaB terms) ≤
      ((FailureModel.sumOfCBDProducts_tailUB etaA etaB terms t₁ : ℚ) /
        (2 : ℚ) ^ expBits etaA etaB terms) := by
    exact (div_le_div_of_nonneg_right hq hdenPos)
  simpa [singleCoeffTailUBQ, expBits] using hdiv

end MultiCoeff

end FIPS203
end KEM
end Crypto
end HeytingLean
