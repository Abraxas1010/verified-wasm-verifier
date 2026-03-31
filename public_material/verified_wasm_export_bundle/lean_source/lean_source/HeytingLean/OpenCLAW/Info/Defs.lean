import HeytingLean.Silicon.Leakage
import HeytingLean.Silicon.Predictability
import HeytingLean.Silicon.Cost

namespace HeytingLean.OpenCLAW.Info

universe u

/-!
# P2PCLAW Information-Theory Claims (Source-Anchored Re-exports)

These theorems are already proved in `HeytingLean.Silicon.*` and are re-exported
here with P2PCLAW-specific aliases.

- source_paper_url: https://arxiv.org/abs/2601.12032
- attribution_status: A-conditional
- claim_status: B-pass
- proof_status: proved
-/

/-- G0-STS-001: Independence implies zero leakage.
Source: arXiv:2601.12032, Section 7.2 Theorem 7.1. -/
theorem independence_implies_zero_leakage
    {S O : Type u} [Fintype S] [Fintype O]
    (P : HeytingLean.Silicon.Run S O)
    (h : HeytingLean.Silicon.Independent (S := S) (O := O) P) :
    HeytingLean.Silicon.Leakage (S := S) (O := O) P = 0 :=
  HeytingLean.Silicon.leakage_eq_zero_of_independent (S := S) (O := O) P h

/-- G0-STS-002: Predictor accuracy above baseline implies non-independence.
Source: arXiv:2601.12032, Section 7.3 Theorem 7.2. -/
theorem accuracy_above_baseline_implies_nonindependence
    {X Y : Type u} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (P : HeytingLean.Silicon.Run X Y) (g : X → Y)
    (hgt :
      HeytingLean.Silicon.Predictability.baseline (X := X) (Y := Y) P <
        HeytingLean.Silicon.Predictability.accuracy (X := X) (Y := Y) P g) :
    ¬ HeytingLean.Silicon.Independent (S := X) (O := Y) P :=
  HeytingLean.Silicon.Predictability.not_independent_of_accuracy_gt_baseline
    (X := X) (Y := Y) P g hgt

/-- G0-STS-003: Energy savings bound in zero-continue regime.
Source: arXiv:2601.12032, Section 7.4 Theorem 7.3. -/
theorem energy_savings_bound
    {Obs Y : Type u} [Fintype Obs] [Fintype Y]
    {n k : Nat} (hn : 0 < n) (hk : k ≤ n)
    (P : HeytingLean.Probability.InfoTheory.FinDist
      (HeytingLean.Silicon.EarlyAbort.Trace (Obs := Obs) n × Y))
    (c : (Fin k → Obs) → Bool)
    (h0 :
      HeytingLean.Silicon.Cost.EarlyAbort.continueProb (Obs := Obs) (Y := Y) hk P c = 0) :
    HeytingLean.Silicon.Cost.EarlyAbort.energySavings
      (Obs := Obs) (Y := Y) (hn := hn) hk P c = 1 - (k : ℝ) / (n : ℝ) :=
  HeytingLean.Silicon.Cost.EarlyAbort.energySavings_eq_of_continueProb_eq_zero
    (Obs := Obs) (Y := Y) (hn := hn) hk P c h0

end HeytingLean.OpenCLAW.Info
