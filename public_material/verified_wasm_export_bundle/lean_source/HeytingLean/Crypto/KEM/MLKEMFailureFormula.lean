import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMFailureBounds

/-!
# ML-KEM decryption-failure probability (formula scaffolding)

This module records **named quantities** used in ML-KEM correctness discussions (FIPS 203),
in a way suitable for later tightening against an explicit probabilistic model.

What is done here:
- Define the decoding threshold and a few simple "bookkeeping" quantities.
- Provide a conservative "formula placeholder" that intentionally matches the published
  FIPS 203 bound structure (`< 2^{-e}`), reusing `reportedFailureBoundQ`.

What is *not* done here:
- Any game/probability model (`PMF`, `Prob`, ROM/QROM).
- Any attempt to replace the published bound axioms; those remain in `MLKEMAxioms.lean`.

External references:
- NIST FIPS 203 (ML-KEM), failure probability discussion + parameter table.
- CRYPTO 2024: "Formally Verifying Kyber Episode V" (ePrint 2024/843) for a mechanized,
  game-based correctness+failure analysis in EasyCrypt (reference-first).
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators

/-- ML-KEM decoding threshold (coarse, spec-level): `⌊q/4⌋` for `q = 3329`. -/
def decodingThreshold : Nat := 3329 / 4

theorem decodingThreshold_eq : decodingThreshold = 832 := by
  decide

/-- Noise term count in the residual `⟨e,r⟩ + e₂ - ⟨s,e₁⟩` (shape-level). -/
def noiseTermCount (p : MLKEM203Params) : Nat :=
  2 * p.k * p.n + 1

theorem noiseTermCount_mlkem768 : noiseTermCount mlkem768 = 2 * 3 * 256 + 1 := rfl

/-- Placeholder upper bound formula: use the published `< 2^{-e}` structure as a rational. -/
noncomputable def failureProbFormula (p : MLKEM203Params) : ℚ :=
  reportedFailureBoundQ p

theorem failureProbFormula_eq_reported (p : MLKEM203Params) :
    failureProbFormula p = reportedFailureBoundQ p := rfl

end FIPS203
end KEM
end Crypto
end HeytingLean

