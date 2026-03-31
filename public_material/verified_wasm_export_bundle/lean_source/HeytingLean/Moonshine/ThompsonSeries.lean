import HeytingLean.Moonshine.GradedRep
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.HahnSeries.Basic

set_option autoImplicit false

namespace HeytingLean.Moonshine

open scoped BigOperators

/-- The trace coefficient in grade `n`. -/
noncomputable def thompsonCoeff {G : Type*} [Group G]
    (R : GradedRep G) (g : G) (n : ℤ) : ℂ :=
  LinearMap.trace ℂ (R.V n) ((R.action n) g)

/--
The Thompson series as a Hahn/Laurent series.

We build it using `HahnSeries.ofSuppBddBelow`, with bounded-below support derived from the
hypothesis `trace_eq_zero_of_lt_lower`.
-/
noncomputable def ThompsonSeries {G : Type*} [Group G]
    (R : GradedRep G) (g : G) : Modular.Laurent ℂ :=
  HahnSeries.ofSuppBddBelow (fun n => thompsonCoeff R g n)
    (HahnSeries.forallLTEqZero_supp_BddBelow (fun n => thompsonCoeff R g n) R.lower (by
      intro n hn
      simpa [thompsonCoeff] using R.trace_eq_zero_of_lt_lower g n hn))

/-- Coefficients of `ThompsonSeries` are exactly `thompsonCoeff`. -/
lemma ThompsonSeries_coeff {G : Type*} [Group G]
    (R : GradedRep G) (g : G) (n : ℤ) :
    (ThompsonSeries R g).coeff n = thompsonCoeff R g n := by
  simp [ThompsonSeries, thompsonCoeff]

/-- For the identity element, the coefficient is the graded dimension (as a complex number). -/
lemma thompsonCoeff_one {G : Type*} [Group G] (R : GradedRep G) (n : ℤ) :
    thompsonCoeff R (1 : G) n = (gradedDim R n : ℂ) := by
  classical
  -- `R.action n` is a monoid hom, so it sends `1` to `1`, i.e. `LinearMap.id`.
  -- Then `trace_id` gives finrank.
  simp [thompsonCoeff, gradedDim]

end HeytingLean.Moonshine
