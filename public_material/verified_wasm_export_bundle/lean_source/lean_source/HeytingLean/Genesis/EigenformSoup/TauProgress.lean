import Mathlib

/-!
# Genesis.EigenformSoup.TauProgress

`κ`/`τ` progress-normalization contracts for LES-Omega.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Signals used in the LEP-style progress metric. -/
structure KappaSignals where
  tps : Rat
  tpsMax : Rat
  vwu : Rat
  ig : Rat

/--
Progress metric:
`κ(t) = 0.3*(TPS/TPS_max) + 0.5*VWU + 0.2*IG`
encoded with exact rationals.
-/
def kappa (s : KappaSignals) : Rat :=
  ((3 : Rat) / 10) * (s.tps / s.tpsMax) +
    ((1 : Rat) / 2) * s.vwu +
    ((1 : Rat) / 5) * s.ig

/-- Cumulative `τ` from a finite `κ` stream. -/
def tauFromKappa (xs : List Rat) : Rat :=
  xs.sum

theorem tauFromKappa_nil : tauFromKappa [] = 0 := by
  simp [tauFromKappa]

theorem tauFromKappa_cons (x : Rat) (xs : List Rat) :
    tauFromKappa (x :: xs) = x + tauFromKappa xs := by
  simp [tauFromKappa]

theorem tauFromKappa_append (xs ys : List Rat) :
    tauFromKappa (xs ++ ys) = tauFromKappa xs + tauFromKappa ys := by
  simp [tauFromKappa, List.sum_append]

theorem tauFromKappa_nonneg
    (xs : List Rat)
    (h : ∀ x ∈ xs, (0 : Rat) ≤ x) :
    (0 : Rat) ≤ tauFromKappa xs := by
  induction xs with
  | nil =>
      simp [tauFromKappa]
  | cons x xs ih =>
      have hx : (0 : Rat) ≤ x := h x (by simp)
      have hxs : ∀ y ∈ xs, (0 : Rat) ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      have ih' := ih hxs
      simpa [tauFromKappa_cons] using add_nonneg hx ih'

end HeytingLean.Genesis.EigenformSoup
