import HeytingLean.Crypto.Lattice.CBDCounts

/-!
# Failure probability (toy computed model)

This module demonstrates a **real computed** tail-bound pipeline for CBD-style noise:

- compute the exact CBD distribution for a chosen `eta` as integer counts;
- convolve it `terms` times to obtain the exact distribution of a sum of independent samples; and
- bound a failure event `|sum| > t` by cross-multiplying counts (no probability axioms).

This is intentionally a *toy* model: it does not yet match the full ML-KEM residual noise model.
It exists to make Gap 3 progress concrete while staying within the repository's strict policy.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FailureToy

open HeytingLean.Crypto.Lattice.CBDCounts

def sumCBDCounts (eta terms : Nat) : CenteredCounts :=
  convolvePowFast (cbdCounts eta) terms

def total (eta terms : Nat) : Nat :=
  totalCount (sumCBDCounts eta terms)

def tail (eta terms t : Nat) : Nat :=
  tailCount (sumCBDCounts eta terms) t

/-!
## A concrete, fully computed example

Parameters:
- `eta = 2`, so a single sample lies in `[-2,2]` and is generated from `2*eta = 4` bits.
- `terms = 4`, so we consider a sum of 4 independent samples.

Total assignments: `2^(2*eta*terms) = 2^16 = 65536`.
-/

def exCounts : CenteredCounts :=
  sumCBDCounts 2 4

theorem ex_totalCount : totalCount exCounts = 65536 := by
  native_decide

theorem ex_tailCount_t6 : tailCount exCounts 6 * 64 ≤ totalCount exCounts := by
  native_decide

end FailureToy
end KEM
end Crypto
end HeytingLean
