import HeytingLean.Crypto.KEM.MLKEMAxioms
import HeytingLean.Crypto.KEM.MLKEMFailureConservative

/-!
# Gap 3 bridge: explicit model assumptions → NIST failure bounds

This file makes the previously-implicit “NIST-style” modeling step explicit:

- We have a fully computed/proved bound for a simplified iid sum-of-products model
  (`MLKEMFailureConservative.lean`).
- The exposed ML-KEM decryption-failure probability `failureProbability` remains model-level and depends
  on explicit simplifications (iid sum-of-products, no full NTT/negacyclic correlation model).

To avoid “silent assumptions”, we record the *heuristic modeling assumption* as a named hypothesis and
prove that, **under that hypothesis**, the NIST bounds follow as theorems.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open ConservativeBounds

namespace FailureModelBridge

private def thresholdQ4 : Nat := 3329 / 4
private def adjustedThreshold (Acomp : Nat) : Nat := thresholdQ4 - Acomp

/-!
## Heuristic assumption (explicit)

`failureProbability` (the real implementation) is assumed to be upper-bounded by the computed proxy
derived from the current simplified model. This encapsulates the “independence / domination”
assumptions that appear (explicitly or implicitly) in published ML-KEM failure analyses.
-/

def failureProbability_le_computed (p : MLKEM203Params) : Prop :=
  failureProbability p ≤ failureProbabilityComputed p (p.k * p.n) thresholdQ4

/-!
## Compression-aware model assumption (explicit)

If `Acomp` bounds the absolute compression noise per coefficient, then a sufficient condition for
`|residual + compression| ≤ thresholdQ4` is `|residual| ≤ thresholdQ4 - Acomp`. We record the
resulting modeling assumption explicitly to avoid hiding this step.
-/

def failureProbability_le_computed_with_compression (p : MLKEM203Params) (Acomp : Nat) : Prop :=
  failureProbability p ≤ failureProbabilityComputed p (p.k * p.n) (adjustedThreshold Acomp)

/-!
## NIST bounds as theorems (under the explicit assumption)
-/

theorem mlkem512_failure_bound_of_model (h : failureProbability_le_computed mlkem512) :
    failureProbability mlkem512 < reportedFailureBoundQ mlkem512 := by
  exact lt_of_le_of_lt h mlkem512_failureProbabilityComputed_lt_reportedFailureBoundQ

theorem mlkem768_failure_bound_of_model (h : failureProbability_le_computed mlkem768) :
    failureProbability mlkem768 < reportedFailureBoundQ mlkem768 := by
  exact lt_of_le_of_lt h mlkem768_failureProbabilityComputed_lt_reportedFailureBoundQ

theorem mlkem1024_failure_bound_of_model (h : failureProbability_le_computed mlkem1024) :
    failureProbability mlkem1024 < reportedFailureBoundQ mlkem1024 := by
  exact lt_of_le_of_lt h mlkem1024_failureProbabilityComputed_lt_reportedFailureBoundQ

theorem failure_bound_of_model_with_compression (p : MLKEM203Params) (Acomp : Nat)
    (h : failureProbability_le_computed_with_compression p Acomp)
    (hbound :
      failureProbabilityComputed p (p.k * p.n) (adjustedThreshold Acomp) < reportedFailureBoundQ p) :
    failureProbability p < reportedFailureBoundQ p := by
  exact lt_of_le_of_lt h hbound

theorem mlkem512_failure_bound_of_model_with_compression
    (h : failureProbability_le_computed_with_compression mlkem512 Acomp512) :
    failureProbability mlkem512 < reportedFailureBoundQ mlkem512 := by
  refine failure_bound_of_model_with_compression (p := mlkem512) (Acomp := Acomp512) h ?_
  exact mlkem512_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ

theorem mlkem768_failure_bound_of_model_with_compression
    (h : failureProbability_le_computed_with_compression mlkem768 Acomp768) :
    failureProbability mlkem768 < reportedFailureBoundQ mlkem768 := by
  refine failure_bound_of_model_with_compression (p := mlkem768) (Acomp := Acomp768) h ?_
  exact mlkem768_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ

theorem mlkem1024_failure_bound_of_model_with_compression
    (h : failureProbability_le_computed_with_compression mlkem1024 Acomp1024) :
    failureProbability mlkem1024 < reportedFailureBoundQ mlkem1024 := by
  refine failure_bound_of_model_with_compression (p := mlkem1024) (Acomp := Acomp1024) h ?_
  exact mlkem1024_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ

end FailureModelBridge

end FIPS203
end KEM
end Crypto
end HeytingLean
