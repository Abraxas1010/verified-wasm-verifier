import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace HeytingLean
namespace Economics
namespace Kelly

noncomputable section

open scoped BigOperators

variable {Ω : Type*}

def returnFactor (f : ℝ) (R : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  1 + f * R n ω

def wealthR (W0 : ℝ) (f : ℝ) (R : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  W0 * ∏ i ∈ Finset.range n, returnFactor f R i ω

@[simp] lemma wealthR_zero (W0 f : ℝ) (R : ℕ → Ω → ℝ) (ω : Ω) :
    wealthR (Ω := Ω) W0 f R 0 ω = W0 := by
  simp [wealthR]

lemma wealthR_succ (W0 f : ℝ) (R : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    wealthR (Ω := Ω) W0 f R (n + 1) ω
      = wealthR (Ω := Ω) W0 f R n ω * returnFactor f R n ω := by
  simp [wealthR, Finset.prod_range_succ, mul_left_comm, mul_comm]

lemma log_wealthR_eq_logW0_add_sum_log_returnFactor
    (W0 f : ℝ) (R : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hW0 : 0 < W0) (hfac : ∀ i < n, 0 < returnFactor f R i ω) :
    Real.log (wealthR (Ω := Ω) W0 f R n ω)
      = Real.log W0 + ∑ i ∈ Finset.range n, Real.log (returnFactor f R i ω) := by
  have hW0' : W0 ≠ 0 := ne_of_gt hW0
  have hfac0 : ∀ i ∈ Finset.range n, returnFactor f R i ω ≠ 0 := by
    intro i hi
    exact ne_of_gt (hfac i (Finset.mem_range.1 hi))
  have hprod0 : (∏ i ∈ Finset.range n, returnFactor f R i ω) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 hfac0
  calc
    Real.log (wealthR (Ω := Ω) W0 f R n ω)
        = Real.log (W0 * ∏ i ∈ Finset.range n, returnFactor f R i ω) := by
            simp [wealthR]
    _ = Real.log W0 + Real.log (∏ i ∈ Finset.range n, returnFactor f R i ω) := by
            simpa using Real.log_mul hW0' hprod0
    _ = Real.log W0 + (∑ i ∈ Finset.range n, Real.log (returnFactor f R i ω)) := by
            congr 1
            simpa using
              (Real.log_prod (s := Finset.range n) (f := fun i => returnFactor f R i ω) hfac0)

lemma log_wealthR_sub_logW0_eq_sum_log_returnFactor
    (W0 f : ℝ) (R : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hW0 : 0 < W0) (hfac : ∀ i < n, 0 < returnFactor f R i ω) :
    Real.log (wealthR (Ω := Ω) W0 f R n ω) - Real.log W0
      = ∑ i ∈ Finset.range n, Real.log (returnFactor f R i ω) := by
  have h := log_wealthR_eq_logW0_add_sum_log_returnFactor
    (Ω := Ω) (W0 := W0) (f := f) (R := R) (n := n) (ω := ω) hW0 hfac
  -- subtract `log W0` on both sides
  calc
    Real.log (wealthR (Ω := Ω) W0 f R n ω) - Real.log W0
        = (Real.log W0 + ∑ i ∈ Finset.range n, Real.log (returnFactor f R i ω)) - Real.log W0 := by
            simp [h]
    _ = ∑ i ∈ Finset.range n, Real.log (returnFactor f R i ω) := by
            simp [sub_eq_add_neg, add_left_comm, add_comm]

end

end Kelly
end Economics
end HeytingLean
