import Mathlib.Tactic
import HeytingLean.Silicon.EarlyAbort

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

namespace Cost

namespace EarlyAbort

variable {Obs Y : Type u} [Fintype Obs] [Fintype Y]

/-- Probability that a prefix-classifier chooses to **continue**. -/
noncomputable def continueProb {n k : ℕ} (hk : k ≤ n)
    (P : FinDist (Silicon.EarlyAbort.Trace (Obs := Obs) n × Y))
    (c : (Fin k → Obs) → Bool) : ℝ := by
  classical
  exact FinDist.probEvent P (fun ty => c (Silicon.EarlyAbort.takePrefix (Obs := Obs) (hk := hk) ty.1) = true)

/-- Expected number of rounds executed by an abort-after-`k` policy on an `n`-round computation. -/
noncomputable def expectedRounds {n k : ℕ} (hk : k ≤ n)
    (P : FinDist (Silicon.EarlyAbort.Trace (Obs := Obs) n × Y))
    (c : (Fin k → Obs) → Bool) : ℝ :=
  (k : ℝ) + ((n - k : ℕ) : ℝ) * continueProb (Obs := Obs) (Y := Y) hk P c

/-- Add a “safety keep rate”: with probability `keepRate`, bypass filtering and always run full `n`. -/
noncomputable def expectedRoundsWithKeepRate (keepRate : ℝ) {n k : ℕ} (hk : k ≤ n)
    (P : FinDist (Silicon.EarlyAbort.Trace (Obs := Obs) n × Y))
    (c : (Fin k → Obs) → Bool) : ℝ :=
  keepRate * (n : ℝ) + (1 - keepRate) * expectedRounds (Obs := Obs) (Y := Y) hk P c

/-- Normalized “energy savings fraction” relative to always running `n` rounds. -/
noncomputable def energySavings {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (P : FinDist (Silicon.EarlyAbort.Trace (Obs := Obs) n × Y))
    (c : (Fin k → Obs) → Bool) : ℝ :=
  let _hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  1 - expectedRounds (Obs := Obs) (Y := Y) hk P c / (n : ℝ)

theorem expectedRounds_eq_of_continueProb_eq_zero {n k : ℕ} (hk : k ≤ n)
    (P : FinDist (Silicon.EarlyAbort.Trace (Obs := Obs) n × Y))
    (c : (Fin k → Obs) → Bool)
    (h0 : continueProb (Obs := Obs) (Y := Y) hk P c = 0) :
    expectedRounds (Obs := Obs) (Y := Y) hk P c = (k : ℝ) := by
  simp [expectedRounds, h0]

theorem energySavings_eq_of_continueProb_eq_zero {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (P : FinDist (Silicon.EarlyAbort.Trace (Obs := Obs) n × Y))
    (c : (Fin k → Obs) → Bool)
    (h0 : continueProb (Obs := Obs) (Y := Y) hk P c = 0) :
    energySavings (Obs := Obs) (Y := Y) (hn := hn) hk P c = 1 - (k : ℝ) / (n : ℝ) := by
  simp [energySavings, expectedRounds, h0]

theorem energySavings_theoreticalMax {n k : ℕ} (hn : 0 < n) :
    (1 - (k : ℝ) / (n : ℝ)) = (n - k : ℝ) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  -- Pure arithmetic.
  field_simp [hn0]

end EarlyAbort

end Cost

end

end Silicon
end HeytingLean
