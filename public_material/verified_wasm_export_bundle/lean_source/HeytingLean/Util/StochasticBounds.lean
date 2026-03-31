import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Stochastic Bounds: Shared Lemma

UTILITY: standalone shared lemma extracted from the pattern used in
`FractalUniverse.Extraction.SpectralComputer.transitionProb_le_one`.

The pattern "single non-negative entry of a unit-sum collection is ≤ 1"
recurs in stochastic matrix bounds. This module provides the general
version, usable by any project working with row-stochastic matrices
or probability distributions over finite types.
-/

namespace HeytingLean.Util

open scoped BigOperators

/-- A single non-negative entry of a collection summing to 1 is at most 1.
    Used by: FractalUniverse.Extraction.SpectralComputer.transitionProb_le_one,
    potentially by Eigen.SafEDMD for projected Gram matrix bounds. -/
theorem single_le_one_of_nonneg_sum_one {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hnonneg : ∀ i, 0 ≤ f i) (hsum : ∑ i ∈ Finset.univ, f i = 1) (j : ι) :
    f j ≤ 1 := by
  calc f j ≤ ∑ i ∈ Finset.univ, f i :=
        Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ j)
    _ = 1 := hsum

end HeytingLean.Util
