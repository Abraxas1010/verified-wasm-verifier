import Mathlib.Data.Rat.Init
import Mathlib.Tactic

namespace HeytingLean.OpenCLAW.Crypto

/-!
# Proof-of-Work Acceptance Predicate and Expected Time

- source_paper_url: https://arxiv.org/abs/2601.09557
- source_location: Section 4.1 Eq (1),(2),(3)
- attribution_status: A-conditional
- claim_status: B-pass
- proof_status: proved (guarded arithmetic model)
-/

/-- G0-SH-001: PoW acceptance predicate (`hash < target`). -/
def powValid (hashOutput target : Nat) : Prop :=
  hashOutput < target

/-- G0-SH-001 theorem anchor: predicate form is definitionally exact. -/
theorem powValid_iff (hashOutput target : Nat) :
    powValid hashOutput target ↔ hashOutput < target :=
  Iff.rfl

/-- Acceptance probability under a uniform `b`-bit hash model and target `target`. -/
def acceptanceProb (b target : Nat) : Rat :=
  (target : Rat) / (2 ^ b : Rat)

/-- Expected number of trials under the same model. -/
def expectedTrials (b target : Nat) : Rat :=
  (2 ^ b : Rat) / target

/-- Expected wall time with hash-rate `H` hashes/second. -/
def expectedWallTime (H : Rat) (b target : Nat) : Rat :=
  expectedTrials b target / H

/-- Geometric-model guard used for expected-time attribution claims. -/
def UniformHashGeometricGuard (b target : Nat) : Prop :=
  expectedTrials b target = 1 / acceptanceProb b target

/-- Algebraic normalization of expected trials under `target > 0`. -/
theorem expected_trials_eq_inv_acceptance (b target : Nat) (ht : 0 < target) :
    expectedTrials b target = 1 / acceptanceProb b target := by
  unfold expectedTrials acceptanceProb
  have htq : (target : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ht)
  field_simp [htq]

/-- G0-SH-002: Expected wall-time formula, guarded by `target > 0` and `H ≠ 0`. -/
theorem expected_wall_time_formula (H : Rat) (b target : Nat) (ht : 0 < target) (hH : H ≠ 0) :
    expectedWallTime H b target = (2 ^ b : Rat) / (target * H) := by
  unfold expectedWallTime expectedTrials
  have htq : (target : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ht)
  field_simp [htq, hH]

/-- Guard witness: the uniform/geometric model is arithmetically consistent for `target > 0`. -/
theorem uniform_hash_geometric_guard_holds (b target : Nat) (ht : 0 < target) :
    UniformHashGeometricGuard b target := by
  exact expected_trials_eq_inv_acceptance b target ht

/-- Sanity check: `b = 32`, `target = 1` simplifies to `2^32 / H`. -/
example (H : Rat) (hH : H ≠ 0) :
    expectedWallTime H 32 1 = (2 ^ 32 : Rat) / H := by
  simpa using expected_wall_time_formula H 32 1 (by decide) hH

/-- Non-degenerate check: `b = 32`, `target = 256` keeps full denominator shape. -/
example (H : Rat) (hH : H ≠ 0) :
    expectedWallTime H 32 256 = (2 ^ 32 : Rat) / (256 * H) := by
  simpa using expected_wall_time_formula H 32 256 (by decide) hH

end HeytingLean.OpenCLAW.Crypto
