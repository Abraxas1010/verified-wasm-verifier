import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.TsumDivsorsAntidiagonal
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

import HeytingLean.Moonshine.Modular.Backport.E2Summable

set_option autoImplicit false

noncomputable section

namespace ModularForm

open TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

lemma eta_tprod_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : ∏' n, (1 - eta_q n z) ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (f := fun n ↦ -eta_q n z) ?_ ?_
  · exact fun i ↦ by simpa using one_sub_eta_q_ne_zero i hz
  · simpa [eta_q, ← summable_norm_iff] using summable_eta_q ⟨z, hz⟩

lemma differentiableAt_eta_tprod {z : ℂ} (hz : z ∈ ℍₒ) :
    DifferentiableAt ℂ (fun x ↦ ∏' n, (1 - eta_q n x)) z := by
  apply (multipliableLocallyUniformlyOn_eta.hasProdLocallyUniformlyOn.differentiableOn ?_
    UpperHalfPlane.isOpen_upperHalfPlaneSet z hz).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  filter_upwards with b
  simpa [Finset.prod_fn] using DifferentiableOn.finset_prod (by fun_prop)

lemma logDeriv_qParam (h : ℝ) (z : ℂ) : logDeriv (𝕢 h) z = 2 * π * I / h := by
  have hq : 𝕢 h = cexp ∘ ((2 * π * I / h) * ·) := by
    ext
    grind [Periodic.qParam]
  rw [hq, logDeriv_comp (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop)]
  simp [logDeriv]

lemma summable_logDeriv_one_sub_eta_q {z : ℂ} (hz : z ∈ ℍₒ) :
    Summable fun i ↦ logDeriv (1 - eta_q i ·) z := by
  have hone (n : ℕ) :
      logDeriv (1 - eta_q n ·) z =
        2 * π * I * (n + 1) * -eta_q n z / (1 - eta_q n z) := by
    have h2 : (fun x ↦ 1 - cexp (2 * ↑π * I * (n + 1) * x)) =
        ((fun w ↦ 1 - 1 * cexp w) ∘ fun x ↦ 2 * ↑π * I * (n + 1) * x) := by aesop
    have h3 : deriv (fun x : ℂ ↦ (2 * π * I * (n + 1) * x)) =
        fun _ ↦ 2 * π * I * (n + 1) := by
      ext y
      simpa using deriv_const_mul (2 * π * I * (n + 1)) (d := fun (x : ℂ) ↦ x) (x := y)
    simp_rw [eta_q_eq_cexp, h2, logDeriv_one_sub_mul_cexp_comp 1
      (g := fun x ↦ (2 * π * I * (n + 1) * x)) (by fun_prop), h3]
    simp
  have hs := summable_norm_pow_mul_geometric_div_one_sub 1
    (UpperHalfPlane.norm_qParam_lt_one 1 ⟨z, hz⟩)
  have hs' : Summable (fun n : ℕ =>
      (n + 1 : ℂ) * ((𝕢 1 z) ^ (n + 1)) / (1 - (𝕢 1 z) ^ (n + 1))) := by
    simpa [one_div] using ((summable_nat_add_iff 1).2 hs)
  have hs'' : Summable (fun n : ℕ =>
      (n + 1 : ℂ) * (eta_q n z) / (1 - eta_q n z)) := by
    refine hs'.congr ?_
    intro n
    simp [eta_q]
  have hsNeg : Summable (fun n : ℕ =>
      (n + 1 : ℂ) * (-eta_q n z) / (1 - eta_q n z)) := by
    refine hs''.neg.congr ?_
    intro n
    ring
  have hsLog : Summable (fun n : ℕ =>
      (2 * π * I) * ((n + 1 : ℂ) * (-eta_q n z) / (1 - eta_q n z))) :=
    hsNeg.mul_left (2 * π * I)
  refine hsLog.congr ?_
  intro n
  simp [hone n, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

open EisensteinSeries in
lemma logDeriv_eta_eq_E2 (z : UpperHalfPlane) : logDeriv eta z = (π * I / 12) * E2 z := by
  let f : ℂ → ℂ := fun w => 𝕢 24 w
  let g : ℂ → ℂ := fun w => ∏' n : ℕ, (1 - eta_q n w)
  change logDeriv (fun w : ℂ => f w * g w) z =
    (π * I / 12) * E2 z
  have hmul :
      logDeriv (fun w : ℂ => f w * g w) z =
        logDeriv f z + logDeriv g z := by
    simpa [f, g] using
      (logDeriv_mul (x := (z : ℂ)) (f := f) (g := g)
        (by simpa [f] using (Periodic.qParam_ne_zero (z : ℂ)))
        (by simpa [g] using (eta_tprod_ne_zero z.2))
        (by fun_prop) (differentiableAt_eta_tprod z.2))
  rw [hmul]
  have hlog := logDeriv_tprod_eq_tsum
    (s := ℍₒ) (x := (⟨(z : ℂ), z.2⟩ : ℍₒ))
    (f := fun i w => 1 - eta_q i w)
    UpperHalfPlane.isOpen_upperHalfPlaneSet
    (fun i => one_sub_eta_q_ne_zero i z.2)
    (by intro i; fun_prop)
    (summable_logDeriv_one_sub_eta_q z.2)
    multipliableLocallyUniformlyOn_eta
    (eta_tprod_ne_zero z.2)
  have hf : logDeriv f z = 2 * π * I / 24 := by
    simpa [f] using (logDeriv_qParam 24 (z : ℂ))
  have hg : logDeriv g z =
      (2 * π * I) * ∑' n : ℕ, (n + 1 : ℂ) * (-eta_q n z) / (1 - eta_q n z) := by
    simpa [g] using hlog.trans (tsum_logDeriv_eta_q (z : ℂ))
  rw [hf, hg]
  simp only [E2, one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul]
  rw [G2_eq_tsum_cexp, riemannZeta_two, ← tsum_pow_div_one_sub_eq_tsum_sigma
    (UpperHalfPlane.norm_exp_two_pi_I_lt_one z), mul_sub, sub_eq_add_neg, mul_add]
  simp [eta_q_eq_pow, ← tsum_mul_left, tsum_pnat_eq_tsum_succ (f := fun n ↦
    n * cexp (2 * π * I * z) ^ n / (1 - cexp (2 * π * I * z) ^ n)), ← tsum_neg]
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]
  ring_nf
  congr
  ext x
  set qx : ℂ := cexp (2 * π * I * z) * cexp (2 * π * I * z) ^ x
  have hq : (1 : ℂ) - qx ≠ 0 := by
    have hr : ‖cexp (2 * π * I * z)‖ < 1 := by
      simpa using (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)
    have hqx_lt : ‖qx‖ < (1 : ℝ) := by
      have hqx_pow : qx = cexp (2 * π * I * z) ^ (x + 1) := by
        simp [qx, pow_succ, mul_assoc, mul_comm]
      rw [hqx_pow, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hr (n := x + 1) (Nat.succ_ne_zero x)
    have hqx_ne_one : qx ≠ (1 : ℂ) := by
      intro h1
      have hnorm : ‖qx‖ = (1 : ℝ) := by simp [h1]
      exact (ne_of_lt hqx_lt) hnorm
    exact sub_ne_zero.mpr (by simpa [eq_comm] using hqx_ne_one)
  have h24 : (24 : ℂ) ≠ 0 := by norm_num
  have hq24 : (24 : ℂ) - qx * (24 : ℂ) ≠ 0 := by
    have hfac : (24 : ℂ) - qx * (24 : ℂ) = (24 : ℂ) * ((1 : ℂ) - qx) := by ring
    rw [hfac]
    exact mul_ne_zero h24 hq
  field_simp [hq, hq24, h24]
  ring

end ModularForm
