import HeytingLean.Crypto.KEM.MLKEMAxioms
import HeytingLean.Crypto.KEM.MLKEMFailureFormula

/-!
# ML-KEM failure probability: bound export

This module re-exports the NIST inequalities from `MLKEMAxioms.lean` under
stable theorem names. A computed/proved bound from a concrete noise model is tracked separately.

What exists today:
- `MLKEMAxioms.failureProbability` and the concrete bounds for ML-KEM-{512,768,1024} are
  exported as theorem-level statements aligned with NIST FIPS 203.

What remains:
- a Lean computation/proof pipeline that derives a bound from a concrete noise model.

External references (for the future computed proof track):
- Formosa Crypto (CRYPTO 2024) artifact: tight failure computations in EasyCrypt.
- "Formally Verified Correctness Bounds" (ACM CCS 2025): Chernoff/convolution proof shape.

Repo policy note:
No new assumptions are introduced here; we only re-export the approved NIST bounds.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open HeytingLean.Crypto.KEM.FIPS203

namespace FailureAxiomExport

theorem mlkem512_failure_bound_assumed :
    failureProbability mlkem512 < reportedFailureBoundQ mlkem512 :=
  mlkem512_failure_bound

theorem mlkem768_failure_bound_assumed :
    failureProbability mlkem768 < reportedFailureBoundQ mlkem768 :=
  mlkem768_failure_bound

theorem mlkem1024_failure_bound_assumed :
    failureProbability mlkem1024 < reportedFailureBoundQ mlkem1024 :=
  mlkem1024_failure_bound

end FailureAxiomExport

end FIPS203
end KEM
end Crypto
end HeytingLean
