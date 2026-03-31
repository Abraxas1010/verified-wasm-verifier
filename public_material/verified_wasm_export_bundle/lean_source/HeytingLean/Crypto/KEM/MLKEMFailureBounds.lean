import HeytingLean.Crypto.KEM.MLKEM203Params

/-!
# ML-KEM reported decryption-failure bounds (structure only)

This file contains the *structure* of the decryption-failure bounds as published in NIST FIPS 203:
each parameter set comes with a reported upper bound of the form `< 2^{-e}` for a fixed exponent
`e` (e.g. `e = 164` for ML-KEM-768).

No probabilistic model or proof is provided here; see `MLKEMAxioms.lean` for the (explicit)
axiomatized inequalities with citations.

Reference: NIST FIPS 203 (ML-KEM), Appendix A / parameter table:
https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.203.pdf
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators

/-- The published exponent `e` for the reported bound `< 2^{-e}` (FIPS 203, parameter table). -/
def reportedFailureExponent (p : MLKEM203Params) : Nat :=
  match p.k with
  | 2 => 139
  | 3 => 164
  | 4 => 174
  | _ => 0

theorem reportedFailureExponent_mlkem512 : reportedFailureExponent mlkem512 = 139 := rfl
theorem reportedFailureExponent_mlkem768 : reportedFailureExponent mlkem768 = 164 := rfl
theorem reportedFailureExponent_mlkem1024 : reportedFailureExponent mlkem1024 = 174 := rfl

/-- A string presentation of the reported failure bound. -/
def reportedFailureBoundString (p : MLKEM203Params) : String :=
  match p.k with
  | 2 => "< 2^{-139}"
  | 3 => "< 2^{-164}"
  | 4 => "< 2^{-174}"
  | _ => "unknown"

/-- A rational-valued version of `2^{-e}` (used only for external-bound bookkeeping). -/
noncomputable def twoNeg (e : Nat) : ℚ :=
  (1 : ℚ) / (2 : ℚ) ^ e

/-- The reported rational upper bound on decryption-failure probability. -/
noncomputable def reportedFailureBoundQ (p : MLKEM203Params) : ℚ :=
  twoNeg (reportedFailureExponent p)

end FIPS203
end KEM
end Crypto
end HeytingLean

