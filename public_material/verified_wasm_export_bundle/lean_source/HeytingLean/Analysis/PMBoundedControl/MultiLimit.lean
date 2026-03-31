import Mathlib
import HeytingLean.Analysis.PMBoundedControl.SoftTransition
import HeytingLean.Eigen.SafEDMD

/-!
# Multi-Limit Completion
-/

namespace HeytingLean
namespace Analysis
namespace PMBoundedControl

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- Componentwise PM completion on finite-dimensional real vectors. -/
def ComponentwiseCompletion (Q_PM : ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => SatRational Q_PM (v i)

/-- Euclidean energy norm used for the multi-limit completion layer. The ambient
`Fin n → ℝ` sup norm is not the paper's intended energy. -/
def euclideanNorm (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (Eigen.sqSum v)

/-- Norm-bounded completion by radial projection onto the closed Euclidean ball of
radius `Q_PM`. -/
def SatNormBounded (Q_PM : ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  if _h : euclideanNorm v ≤ Q_PM then
    v
  else
    (Q_PM / euclideanNorm v) • v

theorem sqSum_nonneg (v : Fin n → ℝ) : 0 ≤ Eigen.sqSum v := by
  unfold Eigen.sqSum
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

theorem euclideanNorm_nonneg (v : Fin n → ℝ) : 0 ≤ euclideanNorm v :=
  Real.sqrt_nonneg _

theorem sqSum_smul (c : ℝ) (v : Fin n → ℝ) :
    Eigen.sqSum (c • v) = c^2 * Eigen.sqSum v := by
  unfold Eigen.sqSum
  calc
    ∑ i, ((c • v) i)^2 = ∑ i, c^2 * (v i)^2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [Pi.smul_apply, pow_two]
      ring
    _ = c^2 * ∑ i, (v i)^2 := by rw [Finset.mul_sum]
    _ = c^2 * Eigen.sqSum v := by rfl

theorem euclideanNorm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (v : Fin n → ℝ) :
    euclideanNorm (c • v) = c * euclideanNorm v := by
  unfold euclideanNorm
  rw [sqSum_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hc]

theorem sat_norm_bounded_identity {Q_PM : ℝ} {v : Fin n → ℝ}
    (h : euclideanNorm v ≤ Q_PM) :
    SatNormBounded Q_PM v = v := by
  simp [SatNormBounded, h]

theorem sat_norm_bounded_le {Q_PM : ℝ} (hQ : 0 ≤ Q_PM) (v : Fin n → ℝ) :
    euclideanNorm (SatNormBounded Q_PM v) ≤ Q_PM := by
  by_cases h : euclideanNorm v ≤ Q_PM
  · simp [SatNormBounded, h]
  · have hv : 0 < euclideanNorm v := by
      have hlt : Q_PM < euclideanNorm v := lt_of_not_ge h
      linarith
    have hscale : 0 ≤ Q_PM / euclideanNorm v := by positivity
    rw [SatNormBounded, dif_neg h, euclideanNorm_smul_of_nonneg hscale]
    exact le_of_eq (by field_simp [hv.ne'])

theorem componentwise_sq_le {Q_PM : ℝ} (hQ : 0 < Q_PM) (v : Fin n → ℝ) (i : Fin n) :
    (ComponentwiseCompletion Q_PM v i)^2 ≤ Q_PM^2 := by
  have hbound : |ComponentwiseCompletion Q_PM v i| ≤ Q_PM := sat_rational_bounded hQ
  have habs : |ComponentwiseCompletion Q_PM v i| ≤ |Q_PM| := by
    simpa [abs_of_pos hQ] using hbound
  exact sq_le_sq.2 habs

theorem componentwise_sqSum_le (Q_PM : ℝ) (hQ : 0 < Q_PM) (v : Fin n → ℝ) :
    Eigen.sqSum (ComponentwiseCompletion Q_PM v) ≤ (n : ℝ) * Q_PM^2 := by
  unfold Eigen.sqSum ComponentwiseCompletion
  calc
    ∑ i, (SatRational Q_PM (v i)) ^ 2 ≤ ∑ i, Q_PM^2 := by
      exact Finset.sum_le_sum (fun i _ => componentwise_sq_le hQ v i)
    _ = (n : ℝ) * Q_PM^2 := by simp

theorem componentwise_implies_norm (Q_PM : ℝ) (hQ : 0 ≤ Q_PM)
    (v : Fin n → ℝ) (hcomp : ∀ i, |v i| ≤ Q_PM) :
    euclideanNorm v ≤ Real.sqrt n * Q_PM := by
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hs : Eigen.sqSum v ≤ (n : ℝ) * Q_PM^2 := by
    unfold Eigen.sqSum
    calc
      ∑ i, (v i)^2 ≤ ∑ i, Q_PM^2 := by
        exact Finset.sum_le_sum (fun i _ => sq_le_sq.2 (by simpa [abs_of_nonneg hQ] using hcomp i))
      _ = (n : ℝ) * Q_PM^2 := by simp
  unfold euclideanNorm
  refine (Real.sqrt_le_iff).2 ?_
  constructor
  · positivity
  · calc
      Eigen.sqSum v ≤ (n : ℝ) * Q_PM^2 := hs
      _ = (Real.sqrt n * Q_PM)^2 := by
            have hsqrt : (Real.sqrt n)^2 = (n : ℝ) := Real.sq_sqrt hn
            nlinarith [hsqrt]

theorem relu_after_componentwise_sqSum_le (Q_PM : ℝ) (hQ : 0 < Q_PM) (v : Fin n → ℝ) :
    Eigen.sqSum (Eigen.reluNucleus n (ComponentwiseCompletion Q_PM v))
      ≤ (n : ℝ) * Q_PM^2 := by
  exact le_trans (Eigen.relu_sqSum_le_sqSum _) (componentwise_sqSum_le Q_PM hQ v)

end

end PMBoundedControl
end Analysis
end HeytingLean
