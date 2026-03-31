import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# AETHER Chebyshev GC Guard Safety

Finite-sample Chebyshev-style guard analysis for liveness values.
-/

namespace HeytingLean.Bridge.Sharma.AetherChebyshev

open scoped BigOperators

/-- Mean over `Fin n`. -/
noncomputable def fmean {n : ℕ} (f : Fin n → Real) : Real :=
  if n = 0 then 0 else (∑ i : Fin n, f i) / n

/-- Variance over `Fin n`. -/
noncomputable def fvariance {n : ℕ} (f : Fin n → Real) : Real :=
  if n = 0 then 0 else (∑ i : Fin n, (f i - fmean f) ^ 2) / n

/-- Standard deviation over `Fin n`. -/
noncomputable def fstddev {n : ℕ} (f : Fin n → Real) : Real :=
  Real.sqrt (fvariance f)

/-- Protection rule: keep objects above the lower-tail threshold. -/
def isProtected {n : ℕ} (f : Fin n → Real) (k : Real) (i : Fin n) : Prop :=
  f i > fmean f - k * fstddev f

/-- Reclaimable objects are below the lower-tail threshold. -/
noncomputable def reclaimable {n : ℕ} (f : Fin n → Real) (k : Real) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter (fun i => ¬ isProtected f k i)

theorem fvariance_nonneg {n : ℕ} (f : Fin n → Real) : 0 ≤ fvariance f := by
  by_cases h : n = 0
  · simp [fvariance, h]
  · have hs : 0 ≤ (∑ i : Fin n, (f i - fmean f) ^ 2) := by
      exact Finset.sum_nonneg (by intro i _; exact sq_nonneg _)
    have hn : 0 ≤ (n : Real) := by exact_mod_cast Nat.zero_le n
    simpa [fvariance, h] using div_nonneg hs hn

theorem fstddev_nonneg {n : ℕ} (f : Fin n → Real) : 0 ≤ fstddev f := by
  exact Real.sqrt_nonneg _

lemma tail_pointwise_sq_bound {n : ℕ} (f : Fin n → Real) (k : Real) (hk : 0 < k)
    {i : Fin n} (hi : i ∈ reclaimable f k) :
    (k * fstddev f) ^ 2 ≤ (f i - fmean f) ^ 2 := by
  let t := k * fstddev f
  have hle : f i ≤ fmean f - t := by
    have hnot : ¬ isProtected f k i := by
      classical
      simpa [reclaimable] using (Finset.mem_filter.mp hi).2
    unfold isProtected at hnot
    simpa [t] using (not_lt.mp hnot)
  have htNonneg : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg (le_of_lt hk) (fstddev_nonneg f)
  have hnonpos : f i - fmean f ≤ 0 := by
    linarith [hle, htNonneg]
  have habsEq : |f i - fmean f| = fmean f - f i := by
    simp [abs_of_nonpos hnonpos]
  have htLeAbs : t ≤ |f i - fmean f| := by
    rw [habsEq]
    linarith [hle]
  have hAbs : |t| ≤ |f i - fmean f| := by
    simpa [abs_of_nonneg htNonneg] using htLeAbs
  have hSq : t ^ 2 ≤ (f i - fmean f) ^ 2 := (sq_le_sq).2 hAbs
  simpa [t] using hSq

/-- Finite lower-tail Chebyshev bound. -/
theorem chebyshev_finite {n : ℕ} (hn : 0 < n) (f : Fin n → Real) (k : Real)
    (hk : 0 < k) (hσ : 0 < fstddev f) :
    ((reclaimable f k).card : Real) ≤ n / k ^ 2 := by
  have hLower :
      ((reclaimable f k).card : Real) * (k * fstddev f) ^ 2 ≤
        Finset.sum (reclaimable f k) (fun i => (f i - fmean f) ^ 2) := by
    calc
      ((reclaimable f k).card : Real) * (k * fstddev f) ^ 2
          = Finset.sum (reclaimable f k) (fun _i => (k * fstddev f) ^ 2) := by simp
      _ ≤ Finset.sum (reclaimable f k) (fun i => (f i - fmean f) ^ 2) := by
        exact Finset.sum_le_sum (fun i hi => tail_pointwise_sq_bound f k hk hi)
  have hUpper :
      Finset.sum (reclaimable f k) (fun i => (f i - fmean f) ^ 2) ≤
        Finset.sum Finset.univ (fun i : Fin n => (f i - fmean f) ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; simp)
      (by intro i _ _; exact sq_nonneg (f i - fmean f))
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hTotal :
      (∑ i : Fin n, (f i - fmean f) ^ 2) = (n : Real) * fvariance f := by
    have hnR : (n : Real) ≠ 0 := by exact_mod_cast hn0
    calc
      (∑ i : Fin n, (f i - fmean f) ^ 2)
          = ((∑ i : Fin n, (f i - fmean f) ^ 2) / n) * n := by
              field_simp [hnR]
      _ = fvariance f * n := by simp [fvariance, hn0]
      _ = (n : Real) * fvariance f := by ring
  have hVarSq : (fstddev f) ^ 2 = fvariance f := by
    unfold fstddev
    simpa [pow_two] using Real.sq_sqrt (fvariance_nonneg f)
  have hMain :
      ((reclaimable f k).card : Real) * (k ^ 2) * (fstddev f) ^ 2
        ≤ (n : Real) * (fstddev f) ^ 2 := by
    calc
      ((reclaimable f k).card : Real) * (k ^ 2) * (fstddev f) ^ 2
          = ((reclaimable f k).card : Real) * (k * fstddev f) ^ 2 := by ring
      _ ≤ (n : Real) * fvariance f := by
        exact le_trans hLower (le_trans hUpper (by simpa using le_of_eq hTotal))
      _ = (n : Real) * (fstddev f) ^ 2 := by simp [hVarSq]
  have hσ2 : 0 < (fstddev f) ^ 2 := by nlinarith [hσ]
  have hNoSigma : ((reclaimable f k).card : Real) * k ^ 2 ≤ (n : Real) := by
    exact le_of_mul_le_mul_right hMain hσ2
  have hk2 : 0 < k ^ 2 := by nlinarith [hk]
  exact (le_div_iff₀ hk2).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hNoSigma)

/-- `k = 2` recovers the 25% upper bound under nonzero variance. -/
theorem gc_25_percent_bound {n : ℕ} (hn : 0 < n) (f : Fin n → Real)
    (hσ : 0 < fstddev f) :
    ((reclaimable f 2).card : Real) ≤ n / 4 := by
  have hChebyshev2 : ((reclaimable f 2).card : Real) ≤ n / (2 : Real) ^ 2 :=
    chebyshev_finite hn f 2 (by norm_num) hσ
  have hpow : (2 : Real) ^ 2 = 4 := by norm_num
  calc
    ((reclaimable f 2).card : Real) ≤ n / (2 : Real) ^ 2 := hChebyshev2
    _ = n / 4 := by simp [hpow]

/-- Uniform scaling factors out of the finite mean. -/
lemma fmean_scale {n : ℕ} (f : Fin n → Real) (gamma : Real) :
    fmean (fun j => gamma * f j) = gamma * fmean f := by
  by_cases h : n = 0
  · simp [fmean, h]
  · have hsum : (∑ j : Fin n, gamma * f j) = gamma * ∑ j : Fin n, f j := by
      simp [Finset.mul_sum]
    have hnR : (n : Real) ≠ 0 := by exact_mod_cast h
    unfold fmean
    simp [h, hsum]
    field_simp [hnR]

/-- Uniform scaling factors out of the finite variance as `gamma^2`. -/
lemma fvariance_scale {n : ℕ} (f : Fin n → Real) (gamma : Real) :
    fvariance (fun j => gamma * f j) = gamma ^ 2 * fvariance f := by
  by_cases h : n = 0
  · simp [fvariance, h]
  · have hnR : (n : Real) ≠ 0 := by exact_mod_cast h
    have hsum :
      (∑ i : Fin n, (gamma * f i - fmean (fun j => gamma * f j)) ^ 2)
        = gamma ^ 2 * (∑ i : Fin n, (f i - fmean f) ^ 2) := by
      calc
        (∑ i : Fin n, (gamma * f i - fmean (fun j => gamma * f j)) ^ 2)
            = ∑ i : Fin n, gamma ^ 2 * (f i - fmean f) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i _
                rw [fmean_scale (f := f) (gamma := gamma)]
                ring
        _ = gamma ^ 2 * (∑ i : Fin n, (f i - fmean f) ^ 2) := by
              simp [Finset.mul_sum]
    unfold fvariance
    simp [h, hsum]
    field_simp [hnR]

/-- Positive scaling factors out of the finite standard deviation. -/
lemma fstddev_scale_pos {n : ℕ} (f : Fin n → Real) (gamma : Real) (hGamma : 0 < gamma) :
    fstddev (fun j => gamma * f j) = gamma * fstddev f := by
  unfold fstddev
  rw [fvariance_scale (f := f) (gamma := gamma)]
  have hGammaNonneg : 0 ≤ gamma := le_of_lt hGamma
  calc
    Real.sqrt (gamma ^ 2 * fvariance f)
        = Real.sqrt (gamma ^ 2) * Real.sqrt (fvariance f) := by
            exact Real.sqrt_mul (sq_nonneg gamma) (fvariance f)
    _ = gamma * Real.sqrt (fvariance f) := by
          simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hGammaNonneg]
    _ = gamma * fstddev f := by rfl

/-- Positive scalar decay preserves guard status. -/
theorem uniform_decay_preserves_guard {n : ℕ} (_hn : 0 < n) (f : Fin n → Real)
    (gamma : Real) (hGamma : 0 < gamma) (k : Real) (_hk : 0 < k) (i : Fin n)
    (h : isProtected f k i) :
    isProtected (fun j => gamma * f j) k i := by
  unfold isProtected at h ⊢
  rw [fmean_scale (f := f) (gamma := gamma), fstddev_scale_pos (f := f) (gamma := gamma) hGamma]
  have hGammaNonneg : 0 ≤ gamma := le_of_lt hGamma
  nlinarith [h]

/-- Cross-object impulse preserves guard when the post-update threshold does not decrease. -/
theorem impulse_strengthens_guard {n : ℕ} (f : Fin n → Real)
    (k : Real) (_hk : 0 < k) (i j : Fin n) (delta : Real) (_hDelta : 0 < delta)
    (h : isProtected f k i) (hij : i ≠ j)
    (hthreshold :
      fmean (Function.update f j (f j + delta)) -
          k * fstddev (Function.update f j (f j + delta))
        ≤ fmean f - k * fstddev f) :
    isProtected (Function.update f j (f j + delta)) k i := by
  unfold isProtected at h ⊢
  have hval : Function.update f j (f j + delta) i = f i := by
    simp [Function.update, hij]
  rw [hval]
  linarith [h, hthreshold]

/-- Touching an object with sufficient explicit margin protects it. -/
theorem touch_protects {n : ℕ} (f : Fin n → Real)
    (k : Real) (_hk : 0 < k) (i : Fin n) (delta : Real)
    (hDelta : f i + delta >
      fmean (Function.update f i (f i + delta)) -
        k * fstddev (Function.update f i (f i + delta))) :
    isProtected (Function.update f i (f i + delta)) k i := by
  unfold isProtected
  simpa [Function.update_self] using hDelta

end HeytingLean.Bridge.Sharma.AetherChebyshev
