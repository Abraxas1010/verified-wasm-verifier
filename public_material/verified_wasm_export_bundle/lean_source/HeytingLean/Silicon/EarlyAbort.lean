import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

namespace EarlyAbort

variable {Obs Y : Type u} [Fintype Obs] [Fintype Y]

/-- A length-`n` observation trace. -/
abbrev Trace (n : ℕ) : Type u :=
  Fin n → Obs

/-- Take the first `k` observations from an `n`-trace (requires `k ≤ n`). -/
def takePrefix {n k : ℕ} (hk : k ≤ n) (t : Trace (Obs := Obs) n) : Fin k → Obs :=
  fun i => t (Fin.castLT i (Nat.lt_of_lt_of_le i.isLt hk))

/-- Success probability of a predictor `g` that reads only the first `k` observations. -/
noncomputable def accuracy {n k : ℕ} (hk : k ≤ n)
    (P : FinDist (Trace (Obs := Obs) n × Y)) (g : (Fin k → Obs) → Y) : ℝ := by
  classical
  exact FinDist.probEvent P (fun ty => g (takePrefix (Obs := Obs) (hk := hk) ty.1) = ty.2)

theorem accuracy_nonneg {n k : ℕ} (hk : k ≤ n)
    (P : FinDist (Trace (Obs := Obs) n × Y)) (g : (Fin k → Obs) → Y) :
    0 ≤ accuracy (Obs := Obs) (Y := Y) hk P g := by
  classical
  simpa [accuracy] using
    (FinDist.probEvent_nonneg (P := P) (E := fun ty => g (takePrefix (Obs := Obs) (hk := hk) ty.1) = ty.2))

theorem accuracy_le_one {n k : ℕ} (hk : k ≤ n)
    (P : FinDist (Trace (Obs := Obs) n × Y)) (g : (Fin k → Obs) → Y) :
    accuracy (Obs := Obs) (Y := Y) hk P g ≤ 1 := by
  classical
  simpa [accuracy] using
    (FinDist.probEvent_le_one (P := P) (E := fun ty => g (takePrefix (Obs := Obs) (hk := hk) ty.1) = ty.2))

end EarlyAbort

end
end Silicon
end HeytingLean

