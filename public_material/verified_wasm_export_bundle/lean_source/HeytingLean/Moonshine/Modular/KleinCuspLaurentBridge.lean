import HeytingLean.Moonshine.Modular.KleinCuspFunction
import HeytingLean.Moonshine.Modular.KleinJ0Laurent

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open scoped BigOperators

/-!
## Cauchy-product bridge for cusp `tsum` expansions (kernel-pure)

`PowerSeries.eval₂` is not available over `ℂ` in Mathlib (it requires `IsLinearTopology ℂ ℂ`).
For Moonshine we instead work directly with `tsum` and prove the algebraic identities we need
using the Cauchy product lemma
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`.

This file is the start of the analytic bridge from
`kleinJ₀_cusp` (a genuine function on the punctured unit disk)
to the formal Laurent series computations in `KleinJ0Laurent.lean`.
-/

def psTerm (ps : PowerSeries ℂ) (q : ℂ) (n : ℕ) : ℂ :=
  ps.coeff n * q ^ n

lemma psTerm_mul_eq_sum_antidiagonal (φ ψ : PowerSeries ℂ) (q : ℂ) (n : ℕ) :
    psTerm (φ * ψ) q n =
      ∑ kl ∈ Finset.antidiagonal n, psTerm φ q kl.1 * psTerm ψ q kl.2 := by
  classical
  dsimp [psTerm]
  -- Expand the coefficient of the product and factor out `q^n`.
  simp [PowerSeries.coeff_mul, Finset.sum_mul]
  refine (Finset.sum_congr rfl ?_)
  intro kl hkl
  have hkl' : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  -- Turn `q^n` into `q^(k+l)` and reassociate.
  calc
    (PowerSeries.coeff kl.1 φ * PowerSeries.coeff kl.2 ψ) * q ^ n
        = (PowerSeries.coeff kl.1 φ * PowerSeries.coeff kl.2 ψ) * q ^ (kl.1 + kl.2) := by
            simp [hkl']
    _ = (PowerSeries.coeff kl.1 φ * q ^ kl.1) * (PowerSeries.coeff kl.2 ψ * q ^ kl.2) := by
          ring_nf

lemma summable_norm_psTerm_mul (φ ψ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖))
    (hψ : Summable (fun n : ℕ => ‖psTerm ψ q n‖)) :
    Summable (fun n : ℕ => ‖psTerm (φ * ψ) q n‖) := by
  classical
  -- Absolute summability of the coefficient convolution.
  have hconv :
      Summable fun n : ℕ =>
        ‖∑ kl ∈ Finset.antidiagonal n, psTerm φ q kl.1 * psTerm ψ q kl.2‖ :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hφ hψ
  -- Rewrite the convolution as `psTerm (φ*ψ)`.
  refine hconv.congr (fun n => ?_)
  simp [psTerm_mul_eq_sum_antidiagonal (φ := φ) (ψ := ψ) (q := q) (n := n)]

private lemma sigma_le_pow_succ (k : ℕ) (n : ℕ) :
    ArithmeticFunction.sigma k n ≤ n ^ (k + 1) := by
  -- `σ_k(n) = ∑_{d|n} d^k ≤ (#divisors n) * n^k ≤ n * n^k = n^(k+1)`.
  classical
  have hsum :
      ArithmeticFunction.sigma k n ≤ n.divisors.card * (n ^ k) := by
    rw [ArithmeticFunction.sigma_apply]
    have : (∑ d ∈ n.divisors, d ^ k) ≤ ∑ _d ∈ n.divisors, n ^ k := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have hdn : d ≤ n := Nat.divisor_le hd
      exact pow_le_pow_left' hdn k
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hcard : n.divisors.card ≤ n := Nat.card_divisors_le_self n
  calc
    ArithmeticFunction.sigma k n ≤ n.divisors.card * (n ^ k) := hsum
    _ ≤ n * (n ^ k) := Nat.mul_le_mul_right _ hcard
    _ = n ^ (k + 1) := by simp [pow_succ, Nat.mul_comm]

private lemma summable_norm_E4_q_expected_term (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖psTerm E4_q_expected q n‖) := by
  -- Absolute convergence via comparison with a polynomial times a geometric series.
  have hq' : ‖(‖q‖ : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)] using hq
  have hgeom : Summable fun n : ℕ => (‖q‖ : ℝ) ^ n := by
    simpa using (summable_geometric_of_norm_lt_one (x := (‖q‖ : ℝ)) hq')
  have hpoly : Summable fun n : ℕ => ((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n := by
    simpa [Real.norm_eq_abs] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (k := 4) (r := (‖q‖ : ℝ)) hq')
  have hpoly' :
      Summable fun n : ℕ => (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n) :=
    hpoly.mul_left (240 : ℝ)
  have hsum :
      Summable fun n : ℕ => (‖q‖ : ℝ) ^ n + (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n) :=
    hgeom.add hpoly'
  -- Compare norms termwise to the summable bound.
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => (‖q‖ : ℝ) ^ n + (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n))
    (g := fun n : ℕ => ‖psTerm E4_q_expected q n‖)
    (fun _ => by positivity) (fun n => ?_) hsum
  -- Prove the pointwise bound.
  rcases eq_or_ne n 0 with rfl | hn
  · simp [psTerm, E4_q_expected_coeff_zero]
  · have hsigma : (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 := by
      have hs' : ArithmeticFunction.sigma 3 n ≤ n ^ (3 + 1) := sigma_le_pow_succ 3 n
      simpa using (show (ArithmeticFunction.sigma 3 n : ℝ) ≤ (n : ℝ) ^ 4 from by
        exact_mod_cast hs')
    have hcoeff :
        ‖E4_q_expected.coeff n‖ ≤ (240 : ℝ) * ((n : ℝ) ^ 4) := by
      have hcn : E4_q_expected.coeff n = (240 : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) := by
        simpa using (E4_q_expected_coeff_of_ne_zero (n := n) hn)
      have : ‖E4_q_expected.coeff n‖ ≤ (240 : ℝ) * (ArithmeticFunction.sigma 3 n : ℝ) := by
        -- `simp` handles `‖(240 : ℂ) * (sigma : ℂ)‖`.
        simp [hcn]
      calc
        ‖E4_q_expected.coeff n‖ ≤ (240 : ℝ) * (ArithmeticFunction.sigma 3 n : ℝ) := this
        _ ≤ (240 : ℝ) * ((n : ℝ) ^ 4) := by gcongr
    calc
      ‖psTerm E4_q_expected q n‖ = ‖E4_q_expected.coeff n‖ * ‖q ^ n‖ := by
        simp [psTerm]
      _ = ‖E4_q_expected.coeff n‖ * (‖q‖ : ℝ) ^ n := by simp [norm_pow]
      _ ≤ (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n) := by
        have : ‖E4_q_expected.coeff n‖ * (‖q‖ : ℝ) ^ n ≤
            ((240 : ℝ) * ((n : ℝ) ^ 4)) * (‖q‖ : ℝ) ^ n := by
          gcongr
        -- Reassociate into `240 * (n^4 * ‖q‖^n)`.
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      _ ≤ (‖q‖ : ℝ) ^ n + (240 : ℝ) * (((n : ℝ) ^ 4) * (‖q‖ : ℝ) ^ n) := by
        exact le_add_of_nonneg_left (by positivity)

private lemma summable_norm_E6_q_expected_term (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖psTerm E6_q_expected q n‖) := by
  have hq' : ‖(‖q‖ : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)] using hq
  have hgeom : Summable fun n : ℕ => (‖q‖ : ℝ) ^ n := by
    simpa using (summable_geometric_of_norm_lt_one (x := (‖q‖ : ℝ)) hq')
  have hpoly : Summable fun n : ℕ => ((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n := by
    simpa [Real.norm_eq_abs] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (k := 6) (r := (‖q‖ : ℝ)) hq')
  have hpoly' :
      Summable fun n : ℕ => (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n) :=
    hpoly.mul_left (504 : ℝ)
  have hsum :
      Summable fun n : ℕ => (‖q‖ : ℝ) ^ n + (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n) :=
    hgeom.add hpoly'
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => (‖q‖ : ℝ) ^ n + (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n))
    (g := fun n : ℕ => ‖psTerm E6_q_expected q n‖)
    (fun _ => by positivity) (fun n => ?_) hsum
  rcases eq_or_ne n 0 with rfl | hn
  · simp [psTerm, E6_q_expected_coeff_zero]
  · have hsigma : (ArithmeticFunction.sigma 5 n : ℝ) ≤ (n : ℝ) ^ 6 := by
      have hs' : ArithmeticFunction.sigma 5 n ≤ n ^ (5 + 1) := sigma_le_pow_succ 5 n
      simpa using (show (ArithmeticFunction.sigma 5 n : ℝ) ≤ (n : ℝ) ^ 6 from by
        exact_mod_cast hs')
    have hcoeff :
        ‖E6_q_expected.coeff n‖ ≤ (504 : ℝ) * ((n : ℝ) ^ 6) := by
      have hcn : E6_q_expected.coeff n = (-504 : ℂ) * (ArithmeticFunction.sigma 5 n : ℂ) := by
        simpa using (E6_q_expected_coeff_of_ne_zero (n := n) hn)
      have : ‖E6_q_expected.coeff n‖ ≤ (504 : ℝ) * (ArithmeticFunction.sigma 5 n : ℝ) := by
        simp [hcn]
      calc
        ‖E6_q_expected.coeff n‖ ≤ (504 : ℝ) * (ArithmeticFunction.sigma 5 n : ℝ) := this
        _ ≤ (504 : ℝ) * ((n : ℝ) ^ 6) := by gcongr
    calc
      ‖psTerm E6_q_expected q n‖ = ‖E6_q_expected.coeff n‖ * ‖q ^ n‖ := by
        simp [psTerm]
      _ = ‖E6_q_expected.coeff n‖ * (‖q‖ : ℝ) ^ n := by simp [norm_pow]
      _ ≤ (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n) := by
        have : ‖E6_q_expected.coeff n‖ * (‖q‖ : ℝ) ^ n ≤
            ((504 : ℝ) * ((n : ℝ) ^ 6)) * (‖q‖ : ℝ) ^ n := by
          gcongr
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      _ ≤ (‖q‖ : ℝ) ^ n + (504 : ℝ) * (((n : ℝ) ^ 6) * (‖q‖ : ℝ) ^ n) := by
        exact le_add_of_nonneg_left (by positivity)

lemma summable_norm_qExpansion₁_E4_term (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E4) q n‖) := by
  -- Transfer absolute convergence from the expected power series.
  simpa [qExpansion₁_E4_eq_expected] using (summable_norm_E4_q_expected_term q hq)

lemma summable_norm_qExpansion₁_E6_term (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E6) q n‖) := by
  simpa [qExpansion₁_E6_eq_expected] using (summable_norm_E6_q_expected_term q hq)

lemma summable_norm_pow_two (φ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖)) :
    Summable (fun n : ℕ => ‖psTerm (φ ^ (2 : ℕ)) q n‖) := by
  simpa [pow_two] using summable_norm_psTerm_mul (φ := φ) (ψ := φ) (q := q) hφ hφ

lemma summable_norm_pow_three (φ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖)) :
    Summable (fun n : ℕ => ‖psTerm (φ ^ (3 : ℕ)) q n‖) := by
  -- `φ^3 = (φ^2) * φ` and use Cauchy product summability twice.
  have h2 : Summable (fun n : ℕ => ‖psTerm (φ ^ (2 : ℕ)) q n‖) :=
    summable_norm_pow_two (φ := φ) (q := q) hφ
  simpa [pow_succ, pow_two, mul_assoc] using
    summable_norm_psTerm_mul (φ := (φ ^ (2 : ℕ))) (ψ := φ) (q := q) h2 hφ

lemma tsum_mul_tsum_eq_tsum_coeff_mul (φ ψ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖))
    (hψ : Summable (fun n : ℕ => ‖psTerm ψ q n‖)) :
    ((∑' n : ℕ, psTerm φ q n) * (∑' n : ℕ, psTerm ψ q n)) =
      ∑' n : ℕ, psTerm (φ * ψ) q n := by
  classical
  -- Cauchy product for absolutely summable series.
  have hmul :
      ((∑' n : ℕ, psTerm φ q n) * (∑' n : ℕ, psTerm ψ q n)) =
        ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, psTerm φ q kl.1 * psTerm ψ q kl.2 :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hφ hψ
  -- Identify the antidiagonal convolution with the `PowerSeries` coefficient formula.
  have hcoeff :
      (fun n : ℕ =>
          (∑ kl ∈ Finset.antidiagonal n, psTerm φ q kl.1 * psTerm ψ q kl.2)) =
        fun n : ℕ => psTerm (φ * ψ) q n := by
    funext n
    -- Expand `psTerm` and rewrite the product coefficient using `PowerSeries.coeff_mul`.
    -- Key point: for `(k,l) ∈ antidiagonal n`, we have `k + l = n` so `q^(k+l) = q^n`.
    dsimp [psTerm]
    -- Rewrite only the RHS coefficient as an antidiagonal sum, then distribute `* q^n`.
    simp [PowerSeries.coeff_mul, Finset.sum_mul]
    refine (Finset.sum_congr rfl ?_)
    intro kl hkl
    have hkl' : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    -- Turn `q^n` into `q^(k+l)` and reassociate.
    calc
      (PowerSeries.coeff kl.1 φ * q ^ kl.1) * (PowerSeries.coeff kl.2 ψ * q ^ kl.2)
          = (PowerSeries.coeff kl.1 φ * PowerSeries.coeff kl.2 ψ) * (q ^ kl.1 * q ^ kl.2) := by
              ring_nf
      _ = (PowerSeries.coeff kl.1 φ * PowerSeries.coeff kl.2 ψ) * q ^ (kl.1 + kl.2) := by
            simp [pow_add, mul_assoc]
      _ = (PowerSeries.coeff kl.1 φ * PowerSeries.coeff kl.2 ψ) * q ^ n := by
            simp [hkl']
  -- Finish by rewriting the RHS of the Cauchy product.
  simpa [hcoeff] using hmul

lemma tsum_pow_two_eq (φ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖)) :
    (∑' n : ℕ, psTerm φ q n) ^ (2 : ℕ) = ∑' n : ℕ, psTerm (φ ^ (2 : ℕ)) q n := by
  simpa [pow_two] using
    (tsum_mul_tsum_eq_tsum_coeff_mul (φ := φ) (ψ := φ) (q := q) hφ hφ)

lemma tsum_pow_three_eq (φ : PowerSeries ℂ) (q : ℂ)
    (hφ : Summable (fun n : ℕ => ‖psTerm φ q n‖)) :
    (∑' n : ℕ, psTerm φ q n) ^ (3 : ℕ) = ∑' n : ℕ, psTerm (φ ^ (3 : ℕ)) q n := by
  have h2 : Summable (fun n : ℕ => ‖psTerm (φ ^ (2 : ℕ)) q n‖) :=
    summable_norm_pow_two (φ := φ) (q := q) hφ
  -- `(tsum φ)^3 = (tsum (φ^2)) * (tsum φ)`.
  calc
    (∑' n : ℕ, psTerm φ q n) ^ (3 : ℕ)
        = ((∑' n : ℕ, psTerm φ q n) ^ (2 : ℕ)) * (∑' n : ℕ, psTerm φ q n) := by
            simp [pow_succ, mul_assoc]
    _ = (∑' n : ℕ, psTerm (φ ^ (2 : ℕ)) q n) * (∑' n : ℕ, psTerm φ q n) := by
          simp [tsum_pow_two_eq (φ := φ) (q := q) hφ]
    _ = ∑' n : ℕ, psTerm ((φ ^ (2 : ℕ)) * φ) q n := by
          simpa using
            (tsum_mul_tsum_eq_tsum_coeff_mul (φ := (φ ^ (2 : ℕ))) (ψ := φ) (q := q) h2 hφ)
    _ = ∑' n : ℕ, psTerm (φ ^ (3 : ℕ)) q n := by
          simp [pow_succ, mul_assoc]

lemma E4_cusp_cube_eq_tsum_pow_three {q : ℂ} (hq : ‖q‖ < 1) :
    (E4_cusp q) ^ (3 : ℕ) = ∑' n : ℕ, psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n := by
  have hE4 : E4_cusp q = ∑' n : ℕ, psTerm (qExpansion₁ E4) q n := by
    simpa [psTerm] using (E4_cusp_eq_tsum_qExpansion₁ (q := q) hq)
  have hs : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E4) q n‖) :=
    summable_norm_qExpansion₁_E4_term q hq
  simpa [hE4] using (tsum_pow_three_eq (φ := qExpansion₁ E4) (q := q) hs)

lemma E6_cusp_sq_eq_tsum_pow_two {q : ℂ} (hq : ‖q‖ < 1) :
    (E6_cusp q) ^ (2 : ℕ) = ∑' n : ℕ, psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n := by
  have hE6 : E6_cusp q = ∑' n : ℕ, psTerm (qExpansion₁ E6) q n := by
    simpa [psTerm] using (E6_cusp_eq_tsum_qExpansion₁ (q := q) hq)
  have hs : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E6) q n‖) :=
    summable_norm_qExpansion₁_E6_term q hq
  simpa [hE6] using (tsum_pow_two_eq (φ := qExpansion₁ E6) (q := q) hs)

lemma kleinD_cusp_eq_tsum_kleinDSeries {q : ℂ} (hq : ‖q‖ < 1) :
    (E4_cusp q) ^ (3 : ℕ) - (E6_cusp q) ^ (2 : ℕ) =
      ∑' n : ℕ, psTerm (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n := by
  have hs4 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E4) q n‖) :=
    summable_norm_qExpansion₁_E4_term q hq
  have hs6 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E6) q n‖) :=
    summable_norm_qExpansion₁_E6_term q hq
  have hs4' : Summable (fun n : ℕ => psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n) :=
    (summable_norm_pow_three (φ := qExpansion₁ E4) (q := q) hs4).of_norm
  have hs6' : Summable (fun n : ℕ => psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n) :=
    (summable_norm_pow_two (φ := qExpansion₁ E6) (q := q) hs6).of_norm
  have hsub :
      (∑' n : ℕ, psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n) -
          ∑' n : ℕ, psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n =
        ∑' n : ℕ,
          (psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n - psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n) := by
    -- `tsum f - tsum g = tsum (f - g)` when both are summable.
    simpa using (hs4'.tsum_sub hs6').symm
  have hsub' :
      (∑' n : ℕ, (PowerSeries.coeff n) ((qExpansion₁ E4) ^ (3 : ℕ)) * q ^ n) -
          ∑' n : ℕ, (PowerSeries.coeff n) ((qExpansion₁ E6) ^ (2 : ℕ)) * q ^ n =
        ∑' n : ℕ,
          ((PowerSeries.coeff n) ((qExpansion₁ E4) ^ (3 : ℕ)) * q ^ n -
            (PowerSeries.coeff n) ((qExpansion₁ E6) ^ (2 : ℕ)) * q ^ n) := by
    simpa [psTerm] using hsub
  -- Rewrite each side as a `tsum` and combine using linearity.
  -- Note: `psTerm` is linear in the `PowerSeries` argument, so termwise subtraction agrees.
  simp [kleinDSeries, E4_cusp_cube_eq_tsum_pow_three (q := q) hq,
    E6_cusp_sq_eq_tsum_pow_two (q := q) hq, hsub', psTerm, sub_mul]

lemma qExpansion₁_E4_coeff_zero : (qExpansion₁ E4).coeff 0 = (1 : ℂ) := by
  simp [qExpansion₁_E4_eq_expected]

lemma qExpansion₁_E6_coeff_zero : (qExpansion₁ E6).coeff 0 = (1 : ℂ) := by
  simp [qExpansion₁_E6_eq_expected]

lemma constantCoeff_qExpansion₁_E4 : PowerSeries.constantCoeff (qExpansion₁ E4) = (1 : ℂ) := by
  -- Convert to coefficient `0`.
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact qExpansion₁_E4_coeff_zero

lemma constantCoeff_qExpansion₁_E6 : PowerSeries.constantCoeff (qExpansion₁ E6) = (1 : ℂ) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact qExpansion₁_E6_coeff_zero

lemma kleinDSeries_coeff_zero :
    (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)).coeff 0 = (0 : ℂ) := by
  -- Work via the ring hom `constantCoeff`, then convert back to `coeff 0`.
  have hcc :
      PowerSeries.constantCoeff (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)) = (0 : ℂ) := by
    simp [kleinDSeries, constantCoeff_qExpansion₁_E4, constantCoeff_qExpansion₁_E6]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcc

lemma psTerm_kleinBSeries_mul_q (E4ps E6ps : PowerSeries ℂ) (q : ℂ) (n : ℕ) :
    psTerm (kleinBSeries E4ps E6ps) q n * q = psTerm (kleinDSeries E4ps E6ps) q (n + 1) := by
  -- `B.coeff n = D.coeff (n+1)`.
  simp [psTerm, kleinBSeries, kleinDSeries, pow_succ, mul_assoc, mul_comm]

lemma tsum_psTerm_kleinDSeries_eq_tsum_succ (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, psTerm (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) =
      ∑' n : ℕ, psTerm (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)) q (n + 1) := by
  -- Use `tsum = f 0 + tsum (n↦f (n+1))` and `f 0 = 0`.
  let f : ℕ → ℂ := fun n => psTerm (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n
  have hs4 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E4) q n‖) :=
    summable_norm_qExpansion₁_E4_term q hq
  have hs6 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E6) q n‖) :=
    summable_norm_qExpansion₁_E6_term q hq
  have hs4' : Summable fun n : ℕ => psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n :=
    (summable_norm_pow_three (φ := qExpansion₁ E4) (q := q) hs4).of_norm
  have hs6' : Summable fun n : ℕ => psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n :=
    (summable_norm_pow_two (φ := qExpansion₁ E6) (q := q) hs6).of_norm
  have hs : Summable f := by
    -- `f n = psTerm(E4^3) - psTerm(E6^2)`.
    refine (hs4'.sub hs6').congr (fun n => ?_)
    simp [f, kleinDSeries, psTerm, sub_mul]
  have h0 : f 0 = 0 := by
    -- Work at the level of `constantCoeff` to avoid `simp` getting stuck on powers.
    simp [f, psTerm, kleinDSeries, constantCoeff_qExpansion₁_E4, constantCoeff_qExpansion₁_E6,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  -- `tsum f = f 0 + tsum (n↦f (n+1))`.
  simpa [f, h0] using hs.tsum_eq_zero_add

lemma tsum_psTerm_kleinDSeries_eq_tsum_kleinBSeries_mul_q (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, psTerm (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) =
      (∑' n : ℕ, psTerm (kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) * q := by
  -- Shift `D` by one (since `D.coeff 0 = 0`) and rewrite `D(n+1)` as `B(n) * q`.
  calc
    (∑' n : ℕ, psTerm (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n)
        = ∑' n : ℕ, psTerm (kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)) q (n + 1) := by
            simpa using (tsum_psTerm_kleinDSeries_eq_tsum_succ (q := q) hq)
    _ = ∑' n : ℕ, psTerm (kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n * q := by
          refine tsum_congr (fun n => ?_)
          simpa [add_comm] using
            (psTerm_kleinBSeries_mul_q (E4ps := qExpansion₁ E4) (E6ps := qExpansion₁ E6) (q := q) n).symm
    _ = (∑' n : ℕ, psTerm (kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) * q := by
          simpa using
            (tsum_mul_right (f := fun n : ℕ =>
              psTerm (kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) (a := q))

/-!
## Removable singularity at `q = 0` for the Klein denominator

We show that `((E4_cusp q)^3 - (E6_cusp q)^2) / q` extends holomorphically to `q = 0`
with value `1728`. This yields the basic Laurent-shape identity for `kleinJ₀_cusp`.
-/

open scoped Topology ENNReal NNReal

open Filter

abbrev kleinDps : PowerSeries ℂ :=
  kleinDSeries (qExpansion₁ E4) (qExpansion₁ E6)

abbrev kleinBps : PowerSeries ℂ :=
  kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)

def powerSeriesFml (ps : PowerSeries ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n => ps.coeff n • ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ

@[simp] lemma powerSeriesFml_coeff (ps : PowerSeries ℂ) (n : ℕ) :
    (powerSeriesFml ps).coeff n = ps.coeff n := by
  classical
  -- Unfold `coeff`; the only nontrivial step is that `mkPiAlgebraFin` at `1` evaluates to `1`.
  dsimp [powerSeriesFml, FormalMultilinearSeries.coeff]
  -- `List.ofFn 1` is a list of ones.
  have hprod : (List.ofFn (1 : Fin n → ℂ)).prod = (1 : ℂ) := by
    change (List.ofFn (fun _ : Fin n => (1 : ℂ))).prod = (1 : ℂ)
    simp
  -- Finish by unfolding the monomial term at `1`.
  simp [hprod]

def kleinDfun (q : ℂ) : ℂ :=
  (E4_cusp q) ^ (3 : ℕ) - (E6_cusp q) ^ (2 : ℕ)

def kleinBfunExt : ℂ → ℂ :=
  dslope kleinDfun 0

/-!
### A local absolute-summability helper for scalar power series coefficients

We use this to justify Cauchy products near `q = 0` without relying on `PowerSeries.eval₂`.
-/

private lemma summable_norm_smul_coeff_of_lt_radius
    (p : FormalMultilinearSeries ℂ ℂ ℂ) {r' : ℝ≥0}
    (hr' : (r' : ℝ≥0∞) < p.radius) :
    ∀ {q : ℂ}, ‖q‖ < r' → Summable (fun n : ℕ => ‖q ^ n • p.coeff n‖) := by
  intro q hq
  -- Majorize by `‖p n‖ * r'^n`, which is summable for `r' < p.radius`.
  have hmaj : Summable (fun n : ℕ => ‖p n‖ * (r' : ℝ) ^ n) :=
    p.summable_norm_mul_pow hr'
  -- Coefficients are bounded by operator norms.
  have hcoeff : ∀ n : ℕ, ‖p.coeff n‖ ≤ ‖p n‖ := by
    intro n
    -- `coeff` is evaluation at `1`, bounded by the operator norm.
    dsimp [FormalMultilinearSeries.coeff]
    have h := (p n).le_opNorm (fun _ : Fin n => (1 : ℂ))
    -- `∏ ‖1‖ = 1`.
    calc
      ‖p n (fun _ : Fin n => (1 : ℂ))‖ ≤ ‖p n‖ * (∏ _i : Fin n, ‖(1 : ℂ)‖) := h
      _ = ‖p n‖ := by simp
  -- Compare termwise with a summable majorant.
  refine hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  have hnq : ‖q‖ ^ n ≤ (r' : ℝ) ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hq) _
  calc
    ‖q ^ n • p.coeff n‖
        = ‖q‖ ^ n * ‖p.coeff n‖ := by
            simp [smul_eq_mul, norm_pow]
    _ ≤ ‖q‖ ^ n * ‖p n‖ := by
          gcongr
          exact hcoeff n
    _ ≤ (r' : ℝ) ^ n * ‖p n‖ := by
          gcongr
    _ = ‖p n‖ * (r' : ℝ) ^ n := by ring

private lemma eventually_summable_norm_smul_coeff
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f p 0) :
    ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖q ^ n • p.coeff n‖) := by
  rcases hf with ⟨r, hr⟩
  -- Pick `r'` with `0 < r' < min 1 r`.
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min zero_lt_one hr.r_pos) with ⟨r', r'pos, hr'⟩
  simp only [lt_min_iff, ENNReal.coe_lt_one_iff, ENNReal.coe_pos] at r'pos hr'
  refine eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) (by simpa using r'pos)) (fun q hq => ?_)
  have hq' : ‖q‖ < r' := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq
  have hradius : (r' : ℝ≥0∞) < p.radius :=
    hr'.2.trans_le hr.r_le
  exact summable_norm_smul_coeff_of_lt_radius (p := p) hradius hq'

lemma hasFPowerSeriesAt_E4_cusp :
    HasFPowerSeriesAt E4_cusp (powerSeriesFml (qExpansion₁ E4)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one) (fun q hq => ?_)
  have hq' : ‖q‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq
  have h := hasSum_qExpansion₁_E4_cusp (q := q) hq'
  -- Convert `•` to `*` and commute to match `q^n • coeff`.
  simpa [powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

lemma hasFPowerSeriesAt_E6_cusp :
    HasFPowerSeriesAt E6_cusp (powerSeriesFml (qExpansion₁ E6)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one) (fun q hq => ?_)
  have hq' : ‖q‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq
  have h := hasSum_qExpansion₁_E6_cusp (q := q) hq'
  simpa [powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

lemma summable_psTerm_kleinDps (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => psTerm kleinDps q n) := by
  have hs4 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E4) q n‖) :=
    summable_norm_qExpansion₁_E4_term q hq
  have hs6 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E6) q n‖) :=
    summable_norm_qExpansion₁_E6_term q hq
  have hs4' : Summable fun n : ℕ => psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n :=
    (summable_norm_pow_three (φ := qExpansion₁ E4) (q := q) hs4).of_norm
  have hs6' : Summable fun n : ℕ => psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n :=
    (summable_norm_pow_two (φ := qExpansion₁ E6) (q := q) hs6).of_norm
  have hs : Summable fun n : ℕ =>
      psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n - psTerm ((qExpansion₁ E6) ^ (2 : ℕ)) q n :=
    hs4'.sub hs6'
  refine hs.congr (fun n => ?_)
  simp [kleinDps, kleinDSeries, psTerm, sub_mul]

lemma hasSum_kleinDfun (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q ^ n • (powerSeriesFml kleinDps).coeff n) (kleinDfun q) := by
  have hs : Summable (fun n : ℕ => psTerm kleinDps q n) :=
    summable_psTerm_kleinDps q hq
  have htsum : kleinDfun q = ∑' n : ℕ, psTerm kleinDps q n := by
    simpa [kleinDfun, kleinDps] using (kleinD_cusp_eq_tsum_kleinDSeries (q := q) hq)
  have : HasSum (fun n : ℕ => psTerm kleinDps q n) (kleinDfun q) := by
    simpa [htsum] using hs.hasSum
  simpa [psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this

lemma hasFPowerSeriesAt_kleinDfun :
    HasFPowerSeriesAt kleinDfun (powerSeriesFml kleinDps) 0 := by
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one) (fun q hq => ?_)
  have hq' : ‖q‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq
  simpa using (hasSum_kleinDfun q hq')

lemma hasFPowerSeriesAt_kleinBfunExt :
    HasFPowerSeriesAt kleinBfunExt (powerSeriesFml kleinDps).fslope 0 := by
  simpa [kleinBfunExt] using
    (HasFPowerSeriesAt.has_fpower_series_dslope_fslope (p := powerSeriesFml kleinDps)
      (f := kleinDfun) (z₀ := (0 : ℂ)) hasFPowerSeriesAt_kleinDfun)

lemma kleinDps_coeff_one : kleinDps.coeff 1 = (1728 : ℂ) := by
  simp [kleinDps, kleinDSeries, qExpansion₁_E4_eq_expected, qExpansion₁_E6_eq_expected,
    coeff_one_E4_cubed_sub_E6_sq_expected]

lemma kleinBfunExt_zero : kleinBfunExt 0 = (1728 : ℂ) := by
  have h0 :
      (powerSeriesFml kleinDps).fslope.coeff 0 = kleinBfunExt 0 := by
    -- Use `coeff_zero` (degree 0 term equals the function value) without triggering `simp` loops.
    dsimp [FormalMultilinearSeries.coeff]
    exact hasFPowerSeriesAt_kleinBfunExt.coeff_zero (v := (1 : Fin 0 → ℂ))
  have : kleinBfunExt 0 = (powerSeriesFml kleinDps).coeff 1 := by
    simpa [FormalMultilinearSeries.coeff_fslope] using h0.symm
  simpa [powerSeriesFml_coeff, kleinDps_coeff_one] using this

lemma eventually_ne_zero_kleinBfunExt :
    ∀ᶠ q in 𝓝 (0 : ℂ), kleinBfunExt q ≠ 0 := by
  have hcont : ContinuousAt kleinBfunExt (0 : ℂ) :=
    hasFPowerSeriesAt_kleinBfunExt.continuousAt
  have h1728 : (1728 : ℂ) ≠ 0 := by
    norm_num
  have h0 : kleinBfunExt (0 : ℂ) ≠ (0 : ℂ) := by
    simp [kleinBfunExt_zero, h1728]
  simpa using (ContinuousAt.eventually_ne hcont h0)

lemma kleinBps_coeff (n : ℕ) : (PowerSeries.coeff n) (kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)) =
    (PowerSeries.coeff (n + 1)) kleinDps := by
  -- `kleinBSeries` is the coefficient shift of `kleinDSeries`.
  simp [kleinDps, kleinBSeries]

lemma eventually_hasSum_kleinBfunExt :
    ∀ᶠ q in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => psTerm (kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) (kleinBfunExt q) := by
  -- Unpack the power series expansion for `kleinBfunExt` and rewrite coefficients.
  have h :=
    (hasFPowerSeriesAt_iff (f := kleinBfunExt) (p := (powerSeriesFml kleinDps).fslope)
      (z₀ := (0 : ℂ))).1 hasFPowerSeriesAt_kleinBfunExt
  -- Rewrite the summand into `psTerm kleinBSeries`.
  refine h.mono (fun q hq => ?_)
  -- `psTerm (kleinBSeries ...) q n` is definitional the coefficient-shifted term of `kleinDps`,
  -- while the `HasFPowerSeriesAt` expansion uses the same coefficients via `fslope`.
  simpa [psTerm, kleinDps, kleinDSeries, kleinBSeries, powerSeriesFml, powerSeriesFml_coeff,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq

lemma hasFPowerSeriesAt_kleinBfunExt' :
    HasFPowerSeriesAt kleinBfunExt (powerSeriesFml kleinBps) 0 := by
  rw [hasFPowerSeriesAt_iff]
  refine (eventually_hasSum_kleinBfunExt).mono (fun q hq => ?_)
  -- Rewrite the summand into `q^n • coeff` form required by `HasFPowerSeriesAt`.
  simpa [kleinBps, psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq

lemma powerSeriesFml_kleinBps_eq_fslope :
    powerSeriesFml kleinBps = (powerSeriesFml kleinDps).fslope := by
  -- `kleinBfunExt` has both power series representations at `0`; use uniqueness in one variable.
  exact (HasFPowerSeriesAt.eq_formalMultilinearSeries
    (x := (0 : ℂ)) (f := kleinBfunExt) hasFPowerSeriesAt_kleinBfunExt' hasFPowerSeriesAt_kleinBfunExt)

lemma eventually_tsum_eq_kleinBfunExt :
    ∀ᶠ q in 𝓝 (0 : ℂ),
      (∑' n : ℕ, psTerm (kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) = kleinBfunExt q := by
  refine (eventually_hasSum_kleinBfunExt).mono (fun q hq => ?_)
  exact hq.tsum_eq

/-!
### The inverse series for `kleinBfunExt` (kernel-pure)

We construct the Taylor expansion of `q ↦ (kleinBfunExt q)⁻¹` at `q = 0` and show that its
coefficients agree with the formal `PowerSeries` inverse `kleinBps⁻¹`. This is a prerequisite
for identifying the analytic Laurent expansion of `kleinJ₀_cusp` with the formal Hahn series
computations in `KleinJ0Laurent.lean`.
-/

noncomputable def kleinBfunInv (q : ℂ) : ℂ :=
  (kleinBfunExt q)⁻¹

lemma analyticAt_kleinBfunInv : AnalyticAt ℂ kleinBfunInv (0 : ℂ) := by
  have hb : AnalyticAt ℂ kleinBfunExt (0 : ℂ) :=
    hasFPowerSeriesAt_kleinBfunExt'.analyticAt
  have h1728 : kleinBfunExt (0 : ℂ) ≠ (0 : ℂ) := by
    simp [kleinBfunExt_zero]
  simpa [kleinBfunInv] using hb.inv h1728

noncomputable def kleinBfunInvFml : FormalMultilinearSeries ℂ ℂ ℂ :=
  Classical.choose analyticAt_kleinBfunInv

lemma hasFPowerSeriesAt_kleinBfunInvFml :
    HasFPowerSeriesAt kleinBfunInv kleinBfunInvFml (0 : ℂ) :=
  Classical.choose_spec analyticAt_kleinBfunInv

noncomputable def kleinBfunInvPS : PowerSeries ℂ :=
  PowerSeries.mk fun n : ℕ => kleinBfunInvFml.coeff n

lemma hasFPowerSeriesAt_kleinBfunInvPS :
    HasFPowerSeriesAt kleinBfunInv (powerSeriesFml kleinBfunInvPS) (0 : ℂ) := by
  have h :=
    (hasFPowerSeriesAt_iff (f := kleinBfunInv) (p := kleinBfunInvFml)
      (z₀ := (0 : ℂ))).1 hasFPowerSeriesAt_kleinBfunInvFml
  rw [hasFPowerSeriesAt_iff]
  refine h.mono (fun q hq => ?_)
  simpa [kleinBfunInvPS, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq

lemma eventually_tsum_eq_kleinBfunInv :
    ∀ᶠ q in 𝓝 (0 : ℂ),
      (∑' n : ℕ, psTerm kleinBfunInvPS q n) = kleinBfunInv q := by
  have h :=
    (hasFPowerSeriesAt_iff (f := kleinBfunInv) (p := powerSeriesFml kleinBfunInvPS)
      (z₀ := (0 : ℂ))).1 hasFPowerSeriesAt_kleinBfunInvPS
  refine h.mono (fun q hq => ?_)
  simpa [psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq.tsum_eq

lemma kleinBps_coeff_zero : kleinBps.coeff 0 = (1728 : ℂ) := by
  have h0 :
      PowerSeries.coeff 0 (kleinBSeries (qExpansion₁ E4) (qExpansion₁ E6)) =
        PowerSeries.coeff (0 + 1) kleinDps :=
    kleinBps_coeff (n := 0)
  simpa [kleinBps, Nat.zero_add] using (h0.trans (by simpa using kleinDps_coeff_one))

lemma constantCoeff_kleinBps : PowerSeries.constantCoeff kleinBps = (1728 : ℂ) := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using kleinBps_coeff_zero

lemma kleinBps_constantCoeff_ne_zero : PowerSeries.constantCoeff kleinBps ≠ (0 : ℂ) := by
  intro h0
  -- Avoid unfolding `kleinBps`; rewrite by the explicit constant coefficient lemma.
  rw [constantCoeff_kleinBps] at h0
  norm_num at h0

private def kleinBprodFun (q : ℂ) : ℂ :=
  ∑' n : ℕ, psTerm (kleinBps * kleinBfunInvPS) q n

private lemma hasFPowerSeriesAt_kleinBprodFun :
    HasFPowerSeriesAt kleinBprodFun (powerSeriesFml (kleinBps * kleinBfunInvPS)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  -- Show `HasSum` on a neighborhood where the defining series is (absolutely) summable.
  have hB : ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖psTerm kleinBps q n‖) := by
    have hs :
        ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖q ^ n • (powerSeriesFml kleinBps).coeff n‖) :=
      eventually_summable_norm_smul_coeff (hf := hasFPowerSeriesAt_kleinBfunExt')
    refine hs.mono (fun q hq => ?_)
    simpa [psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq
  have hInv : ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖psTerm kleinBfunInvPS q n‖) := by
    have hs :
        ∀ᶠ q in 𝓝 (0 : ℂ),
          Summable (fun n : ℕ => ‖q ^ n • (powerSeriesFml kleinBfunInvPS).coeff n‖) :=
      eventually_summable_norm_smul_coeff (hf := hasFPowerSeriesAt_kleinBfunInvPS)
    refine hs.mono (fun q hq => ?_)
    simpa [psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq
  refine (hB.and hInv).mono (fun q hq => ?_)
  have hsProdNorm :
      Summable (fun n : ℕ => ‖psTerm (kleinBps * kleinBfunInvPS) q n‖) :=
    summable_norm_psTerm_mul (φ := kleinBps) (ψ := kleinBfunInvPS) (q := q) hq.1 hq.2
  have hsProd : Summable (fun n : ℕ => psTerm (kleinBps * kleinBfunInvPS) q n) :=
    hsProdNorm.of_norm
  -- Convert to `HasSum` with sum equal to the defining `tsum`.
  simpa [kleinBprodFun, psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    (hsProd.hasSum)

private lemma eventually_kleinBprodFun_eq_one :
    ∀ᶠ q in 𝓝 (0 : ℂ), kleinBprodFun q = (1 : ℂ) := by
  have hBtsum : ∀ᶠ q in 𝓝 (0 : ℂ), (∑' n : ℕ, psTerm kleinBps q n) = kleinBfunExt q := by
    have h :=
      (hasFPowerSeriesAt_iff (f := kleinBfunExt) (p := powerSeriesFml kleinBps)
        (z₀ := (0 : ℂ))).1 hasFPowerSeriesAt_kleinBfunExt'
    refine h.mono (fun q hq => ?_)
    simpa [psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq.tsum_eq
  have hInvtsum : ∀ᶠ q in 𝓝 (0 : ℂ), (∑' n : ℕ, psTerm kleinBfunInvPS q n) = kleinBfunInv q :=
    eventually_tsum_eq_kleinBfunInv
  have hBabs : ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖psTerm kleinBps q n‖) := by
    have hs :
        ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖q ^ n • (powerSeriesFml kleinBps).coeff n‖) :=
      eventually_summable_norm_smul_coeff (hf := hasFPowerSeriesAt_kleinBfunExt')
    refine hs.mono (fun q hq => ?_)
    simpa [psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq
  have hInvabs : ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖psTerm kleinBfunInvPS q n‖) := by
    have hs :
        ∀ᶠ q in 𝓝 (0 : ℂ),
          Summable (fun n : ℕ => ‖q ^ n • (powerSeriesFml kleinBfunInvPS).coeff n‖) :=
      eventually_summable_norm_smul_coeff (hf := hasFPowerSeriesAt_kleinBfunInvPS)
    refine hs.mono (fun q hq => ?_)
    simpa [psTerm, powerSeriesFml_coeff, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq
  have hneq : ∀ᶠ q in 𝓝 (0 : ℂ), kleinBfunExt q ≠ 0 := eventually_ne_zero_kleinBfunExt
  refine (((hBtsum.and hInvtsum).and (hBabs.and hInvabs)).and hneq).mono (fun q h => ?_)
  rcases h with ⟨⟨⟨hBtsum, hInvtsum⟩, ⟨hBabs, hInvabs⟩⟩, hneq⟩
  have hmul :
      ((∑' n : ℕ, psTerm kleinBps q n) * (∑' n : ℕ, psTerm kleinBfunInvPS q n)) =
        ∑' n : ℕ, psTerm (kleinBps * kleinBfunInvPS) q n :=
    tsum_mul_tsum_eq_tsum_coeff_mul (φ := kleinBps) (ψ := kleinBfunInvPS) (q := q) hBabs hInvabs
  calc
    kleinBprodFun q
        = ∑' n : ℕ, psTerm (kleinBps * kleinBfunInvPS) q n := by rfl
    _ = (∑' n : ℕ, psTerm kleinBps q n) * (∑' n : ℕ, psTerm kleinBfunInvPS q n) := by
          simp [hmul]
    _ = kleinBfunExt q * kleinBfunInv q := by simp [hBtsum, hInvtsum]
    _ = (1 : ℂ) := by simp [kleinBfunInv, hneq]

private lemma kleinBps_mul_kleinBfunInvPS_eq_one :
    kleinBps * kleinBfunInvPS = (1 : PowerSeries ℂ) := by
  -- Compare power series representations of a locally constant function.
  have hConst :
      HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ)) (powerSeriesFml (PowerSeries.C (1 : ℂ))) (0 : ℂ) := by
    rw [hasFPowerSeriesAt_iff]
    refine Filter.Eventually.of_forall (fun q => ?_)
    have : HasSum (fun n : ℕ => q ^ n • (powerSeriesFml (PowerSeries.C (1 : ℂ))).coeff n) (1 : ℂ) := by
      simpa [powerSeriesFml_coeff, PowerSeries.coeff_C, smul_eq_mul] using
        (hasSum_single 0 (fun n hn => by simp [hn]))
    simpa using this
  have hProd :
      HasFPowerSeriesAt kleinBprodFun (powerSeriesFml (kleinBps * kleinBfunInvPS)) (0 : ℂ) :=
    hasFPowerSeriesAt_kleinBprodFun
  have heq : ∀ᶠ q in 𝓝 (0 : ℂ), kleinBprodFun q = (1 : ℂ) :=
    eventually_kleinBprodFun_eq_one
  have hpq :
      powerSeriesFml (kleinBps * kleinBfunInvPS) = powerSeriesFml (PowerSeries.C (1 : ℂ)) :=
    HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hProd hConst heq
  ext n
  have := congrArg (fun p => p.coeff n) hpq
  simpa [powerSeriesFml_coeff] using this

lemma kleinBfunInvPS_eq_kleinBps_inv : kleinBfunInvPS = kleinBps⁻¹ := by
  have hcc : PowerSeries.constantCoeff kleinBps ≠ (0 : ℂ) := kleinBps_constantCoeff_ne_zero
  have hmul : kleinBfunInvPS * kleinBps = (1 : PowerSeries ℂ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using kleinBps_mul_kleinBfunInvPS_eq_one
  -- `ψ⁻¹ = φ ↔ φ * ψ = 1`.
  exact ((PowerSeries.inv_eq_iff_mul_eq_one (ψ := kleinBps) (φ := kleinBfunInvPS) hcc).2 hmul).symm

lemma eventually_tsum_eq_kleinBps_inv :
    ∀ᶠ q in 𝓝 (0 : ℂ),
      (∑' n : ℕ, psTerm (kleinBps⁻¹) q n) = kleinBfunInv q := by
  -- Rewrite via the chosen inverse series.
  simpa [kleinBfunInvPS_eq_kleinBps_inv] using eventually_tsum_eq_kleinBfunInv

lemma eventually_summable_norm_psTerm_kleinASeries :
    ∀ᶠ q in 𝓝 (0 : ℂ),
      Summable (fun n : ℕ =>
        ‖psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n‖) := by
  -- Work on a neighborhood where `‖q‖ < 1` (for `E4_cusp`) and the inverse-series norm terms are summable.
  have hq1 : ∀ᶠ q in 𝓝 (0 : ℂ), ‖q‖ < 1 := by
    refine eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one) (fun q hq => ?_)
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq
  have hInvAbs : ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖psTerm (kleinBps⁻¹) q n‖) := by
    -- Absolute convergence follows from the analytic power series for `kleinBfunInv`.
    have hs :
        ∀ᶠ q in 𝓝 (0 : ℂ),
          Summable (fun n : ℕ => ‖q ^ n • (powerSeriesFml kleinBfunInvPS).coeff n‖) :=
      eventually_summable_norm_smul_coeff (hf := hasFPowerSeriesAt_kleinBfunInvPS)
    refine hs.mono (fun q hq => ?_)
    -- Rewrite coefficients and use `kleinBfunInvPS = kleinBps⁻¹`.
    simpa [kleinBfunInvPS_eq_kleinBps_inv, psTerm, powerSeriesFml_coeff, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hq
  refine (hq1.and hInvAbs).mono (fun q h => ?_)
  rcases h with ⟨hq1, hInvAbs⟩
  have hs4 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E4) q n‖) :=
    summable_norm_qExpansion₁_E4_term q hq1
  have hs4' : Summable (fun n : ℕ => ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖) :=
    summable_norm_pow_three (φ := qExpansion₁ E4) (q := q) hs4
  have hsMul :
      Summable (fun n : ℕ =>
        ‖psTerm (((qExpansion₁ E4) ^ (3 : ℕ)) * (kleinBps⁻¹)) q n‖) :=
    summable_norm_psTerm_mul (φ := (qExpansion₁ E4) ^ (3 : ℕ)) (ψ := kleinBps⁻¹) (q := q) hs4' hInvAbs
  -- Scale by the constant factor `1728`.
  have hterm :
      (fun n : ℕ => ‖psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n‖) =
        fun n : ℕ =>
          ‖(1728 : ℂ)‖ * ‖psTerm (((qExpansion₁ E4) ^ (3 : ℕ)) * (kleinBps⁻¹)) q n‖ := by
    funext n
    -- `psTerm` sees `C 1728` as coefficientwise scaling.
    simp [kleinASeries, kleinBps, psTerm, mul_assoc, PowerSeries.coeff_C_mul]
  -- `Summable` is stable under multiplying by a constant.
  simpa [hterm] using hsMul.mul_left ‖(1728 : ℂ)‖

noncomputable def kleinAfun (q : ℂ) : ℂ :=
  (1728 : ℂ) * (E4_cusp q) ^ (3 : ℕ) * kleinBfunInv q

lemma eventually_tsum_eq_kleinAfun :
    ∀ᶠ q in 𝓝 (0 : ℂ),
      (∑' n : ℕ, psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) = kleinAfun q := by
  -- Work on a neighborhood where `‖q‖ < 1` (for `E4_cusp`) and the inverse series converges.
  have hq1 : ∀ᶠ q in 𝓝 (0 : ℂ), ‖q‖ < 1 := by
    refine eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one) (fun q hq => ?_)
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hq
  have hInv : ∀ᶠ q in 𝓝 (0 : ℂ),
      (∑' n : ℕ, psTerm (kleinBps⁻¹) q n) = kleinBfunInv q :=
    eventually_tsum_eq_kleinBps_inv
  have hInvAbs : ∀ᶠ q in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖psTerm (kleinBps⁻¹) q n‖) := by
    -- Absolute convergence follows from the analytic power series for `kleinBfunInv`.
    have hs :
        ∀ᶠ q in 𝓝 (0 : ℂ),
          Summable (fun n : ℕ => ‖q ^ n • (powerSeriesFml kleinBfunInvPS).coeff n‖) :=
      eventually_summable_norm_smul_coeff (hf := hasFPowerSeriesAt_kleinBfunInvPS)
    refine hs.mono (fun q hq => ?_)
    -- Rewrite coefficients and use `kleinBfunInvPS = kleinBps⁻¹`.
    simpa [kleinBfunInvPS_eq_kleinBps_inv, psTerm, powerSeriesFml_coeff, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hq
  refine (hq1.and (hInv.and hInvAbs)).mono (fun q h => ?_)
  rcases h with ⟨hq1, hInv, hInvAbs⟩
  -- Use the Cauchy product bridge for the non-constant factors, avoiding coefficient-level
  -- expansion of the constant series (which creates nested antidiagonal sums).
  have hE4 : (E4_cusp q) ^ (3 : ℕ) = ∑' n : ℕ, psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n :=
    E4_cusp_cube_eq_tsum_pow_three (q := q) hq1
  have hs4 : Summable (fun n : ℕ => ‖psTerm (qExpansion₁ E4) q n‖) :=
    summable_norm_qExpansion₁_E4_term q hq1
  have hs4' : Summable (fun n : ℕ => ‖psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n‖) :=
    summable_norm_pow_three (φ := qExpansion₁ E4) (q := q) hs4
  have hmul :
      ((∑' n : ℕ, psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n) * (∑' n : ℕ, psTerm (kleinBps⁻¹) q n)) =
        ∑' n : ℕ, psTerm (((qExpansion₁ E4) ^ (3 : ℕ)) * (kleinBps⁻¹)) q n :=
    tsum_mul_tsum_eq_tsum_coeff_mul (φ := (qExpansion₁ E4) ^ (3 : ℕ)) (ψ := kleinBps⁻¹) (q := q)
      hs4' hInvAbs
  have hscale :
      (∑' n : ℕ, psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) =
        (1728 : ℂ) * (∑' n : ℕ, psTerm (((qExpansion₁ E4) ^ (3 : ℕ)) * (kleinBps⁻¹)) q n) := by
    calc
      (∑' n : ℕ, psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n)
          =
          ∑' n : ℕ, (1728 : ℂ) * psTerm (((qExpansion₁ E4) ^ (3 : ℕ)) * (kleinBps⁻¹)) q n := by
            refine tsum_congr (fun n => ?_)
            -- `coeff n (C c * φ) = c * coeff n φ`.
            simp [kleinASeries, kleinBps, psTerm, mul_assoc, PowerSeries.coeff_C_mul]
      _ = (1728 : ℂ) * (∑' n : ℕ, psTerm (((qExpansion₁ E4) ^ (3 : ℕ)) * (kleinBps⁻¹)) q n) := by
            simpa using (tsum_mul_left
              (f := fun n : ℕ => psTerm (((qExpansion₁ E4) ^ (3 : ℕ)) * (kleinBps⁻¹)) q n)
              (a := (1728 : ℂ)))
  -- Now substitute the Cauchy product and the analytic equalities.
  calc
    (∑' n : ℕ, psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n)
        = (1728 : ℂ) * ((∑' n : ℕ, psTerm ((qExpansion₁ E4) ^ (3 : ℕ)) q n) *
            (∑' n : ℕ, psTerm (kleinBps⁻¹) q n)) := by
          simpa using (hscale.trans (congrArg (fun t => (1728 : ℂ) * t) hmul.symm))
    _ = (1728 : ℂ) * ((E4_cusp q) ^ (3 : ℕ) * kleinBfunInv q) := by
          -- Use `hE4` in the reverse direction.
          simp [← hE4, hInv]
    _ = kleinAfun q := by
          simp [kleinAfun, mul_assoc]

lemma kleinDfun_zero : kleinDfun 0 = 0 := by
  have hq : ‖(0 : ℂ)‖ < 1 := by simp
  have htsum : kleinDfun 0 = ∑' n : ℕ, psTerm kleinDps 0 n := by
    simpa [kleinDfun, kleinDps] using (kleinD_cusp_eq_tsum_kleinDSeries (q := (0 : ℂ)) hq)
  have hcoeff0 : kleinDps.coeff 0 = 0 := by
    simpa [kleinDps] using kleinDSeries_coeff_zero
  have hterm : ∀ n : ℕ, psTerm kleinDps 0 n = 0 := by
    intro n
    cases n with
    | zero =>
        simp [psTerm, hcoeff0]
    | succ n =>
        simp [psTerm]
  calc
    kleinDfun 0 = ∑' n : ℕ, psTerm kleinDps 0 n := htsum
    _ = ∑' _n : ℕ, (0 : ℂ) := by
          refine tsum_congr (fun n => ?_)
          simp [hterm n]
    _ = (0 : ℂ) := by simp

lemma kleinBfunExt_eq_div (q : ℂ) (hq : q ≠ 0) :
    kleinBfunExt q = q⁻¹ * kleinDfun q := by
  -- Away from `0`, `dslope` agrees with `slope`.
  simp [kleinBfunExt, dslope_of_ne, hq, slope, kleinDfun_zero, smul_eq_mul]

lemma kleinDfun_eq_mul_kleinBfunExt (q : ℂ) (hq : q ≠ 0) :
    kleinDfun q = q * kleinBfunExt q := by
  have h := kleinBfunExt_eq_div (q := q) hq
  -- Multiply through by `q` and simplify.
  calc
    kleinDfun q = q * (q⁻¹ * kleinDfun q) := by simp [hq]
    _ = q * kleinBfunExt q := by simp [h]

lemma kleinJ_cusp_eq_qInv_mul (q : ℂ) (hq : q ≠ 0) :
    kleinJ_cusp q =
      q⁻¹ * ((1728 : ℂ) * (E4_cusp q) ^ (3 : ℕ) * (kleinBfunExt q)⁻¹) := by
  have hden : (E4_cusp q) ^ (3 : ℕ) - (E6_cusp q) ^ (2 : ℕ) = q * kleinBfunExt q := by
    simpa [kleinDfun] using (kleinDfun_eq_mul_kleinBfunExt (q := q) hq)
  -- Rewrite the denominator and reassociate.
  simp [kleinJ_cusp, hden, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma kleinJ₀_cusp_eq_qInv_mul (q : ℂ) (hq : q ≠ 0) :
    kleinJ₀_cusp q =
      q⁻¹ * ((1728 : ℂ) * (E4_cusp q) ^ (3 : ℕ) * (kleinBfunExt q)⁻¹) - 744 := by
  simp [kleinJ₀_cusp, kleinJ_cusp_eq_qInv_mul (q := q) hq, sub_eq_add_neg]

lemma eventually_kleinJ₀_cusp_eq_qInv_tsum_kleinASeries :
    ∀ᶠ q in 𝓝 (0 : ℂ), q ≠ 0 →
      kleinJ₀_cusp q =
        q⁻¹ * (∑' n : ℕ, psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) - 744 := by
  have hA : ∀ᶠ q in 𝓝 (0 : ℂ),
      (∑' n : ℕ, psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) = kleinAfun q :=
    eventually_tsum_eq_kleinAfun
  refine hA.mono (fun q hA hq0 => ?_)
  have : kleinJ₀_cusp q = q⁻¹ * ((1728 : ℂ) * (E4_cusp q) ^ (3 : ℕ) * kleinBfunInv q) - 744 := by
    simpa [kleinBfunInv] using (kleinJ₀_cusp_eq_qInv_mul (q := q) hq0)
  have hthis : kleinJ₀_cusp q = q⁻¹ * kleinAfun q - 744 := by
    simpa [kleinAfun, mul_assoc] using this
  simpa [hA] using hthis

theorem kleinJ₀_laurent_sprint_artifact :
    (∀ᶠ q in 𝓝 (0 : ℂ), q ≠ 0 →
        kleinJ₀_cusp q =
          q⁻¹ * (∑' n : ℕ, psTerm (kleinASeries (qExpansion₁ E4) (qExpansion₁ E6)) q n) - 744) ∧
      ((kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff (-1) = J_q.coeff (-1) ∧
        (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 0 = J_q.coeff 0 ∧
        (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 1 = J_q.coeff 1 ∧
        (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 2 = J_q.coeff 2) := by
  refine ⟨eventually_kleinJ₀_cusp_eq_qInv_tsum_kleinASeries, ?_⟩
  simpa using kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q

end HeytingLean.Moonshine.Modular
