import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMFailureBounds
import HeytingLean.Crypto.KEM.MLKEMFailureConservative
import HeytingLean.Crypto.KEM.MLKEMProofLine

/-!
# ML-KEM external assumptions (FO security + numeric failure bounds)

This repository enforces a strict “no placeholder proofs” policy for Lean files and generally avoids
global declarations. This module keeps stable theorem names for two classes of results:

1. **Fujisaki–Okamoto (FO) transform security**: a game-based reduction (IND-CPA → IND-CCA) in the
   Random Oracle Model (and, for post-quantum, in variants of the QROM).
2. **Published numerical decryption-failure bounds** for concrete parameter sets (e.g. ML-KEM-768
   has failure probability `< 2^{-164}`).

The numeric failure side is now instantiated via the conservative computed model in
`MLKEMFailureConservative.lean`. The FO side remains a theorem-level shell because
the external EasyCrypt proof line has not yet been fully reimplemented in Lean.

## References

- Hofheinz, Hövelmanns, Kiltz: *A Modular Analysis of the Fujisaki–Okamoto Transformation*,
  TCC 2017. Eprint: https://eprint.iacr.org/2017/604
- NIST FIPS 203: *Module-Lattice-Based Key-Encapsulation Mechanism Standard (ML-KEM)*,
  parameter sets + reported failure bounds:
  https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.203.pdf
- NIST SP 800-227 (supporting context for KEM security analysis): https://csrc.nist.gov
- ML-KEM is based on CRYSTALS-Kyber; failure analysis background: https://eprint.iacr.org/2022/472
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

/-!
## Failure probability: computed conservative model

We expose `failureProbability` via the existing computed conservative model.
The bound *structure* (`reportedFailureExponent`, etc.) lives in `MLKEMFailureBounds.lean`.

### Scope note

This model is conservative and computed, but it is still a model. A full implementation-faithful
bridge remains future work.

Tracking: `conjectures/mlkem_failure_probability_bounds.json` + the active session under `sessions/active/`.
-/

/-- Abstract (implementation-dependent) decryption-failure probability `δ(p)`. -/
noncomputable def failureProbability (p : MLKEM203Params) : ℚ :=
  ConservativeBounds.failureProbabilityComputed p (p.k * p.n) ConservativeBounds.thresholdQ4

/-- Published NIST bound for ML-KEM-512 decryption-failure probability. -/
theorem mlkem512_failure_bound :
    failureProbability mlkem512 < reportedFailureBoundQ mlkem512 := by
  simpa [failureProbability] using ConservativeBounds.mlkem512_failureProbabilityComputed_lt_reportedFailureBoundQ

/-- Published NIST bound for ML-KEM-768 decryption-failure probability. -/
theorem mlkem768_failure_bound :
    failureProbability mlkem768 < reportedFailureBoundQ mlkem768 := by
  simpa [failureProbability] using ConservativeBounds.mlkem768_failureProbabilityComputed_lt_reportedFailureBoundQ

/-- Published NIST bound for ML-KEM-1024 decryption-failure probability. -/
theorem mlkem1024_failure_bound :
    failureProbability mlkem1024 < reportedFailureBoundQ mlkem1024 := by
  simpa [failureProbability] using ConservativeBounds.mlkem1024_failureProbabilityComputed_lt_reportedFailureBoundQ

/-!
## Fujisaki–Okamoto (FO) security: theorem-level shell

The full FO theorem is a game-based reduction proof that requires a full ROM/QROM framework,
adversary modeling (PPT/QPT), and advantage definitions. We record a **minimal hook** here so
downstream modules can reference “FO security is assumed from the literature”.
-/

/-- Imported ML-KEM IND-CCA proof-line witness from the external Episode V corpus. -/
noncomputable def mlkem_ind_cca_assumed (p : MLKEM203Params) :
    ProofLine.StatementBundle p := by
  exact ProofLine.importedEpisodeV p

end FIPS203
end KEM
end Crypto
end HeytingLean
