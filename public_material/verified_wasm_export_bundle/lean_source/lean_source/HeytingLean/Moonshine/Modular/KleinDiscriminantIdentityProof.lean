import HeytingLean.Moonshine.Modular.KleinDiscriminantRoute
import Mathlib.Analysis.NormedSpace.MultipliableUniformlyOn
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane
open Filter
open scoped CongruenceSubgroup

/-!
Auxiliary proof spine for closing the A4 contract.

This file does not yet prove the punctured-disk discriminant identity. It packages
the target into an explicit Euler-product normal form:

`q⁻¹ * Delta_cusp q = (∏' n, (1 - q^(n+1)))^24` for `q ≠ 0`.

That removes one symbolic layer from the remaining contract and gives a cleaner
analytic target for subsequent uniqueness/series arguments.
-/

/-- The Euler-product factor appearing in `Delta_cusp` after removing the leading `q`. -/
noncomputable def deltaEulerProduct (q : ℂ) : ℂ :=
  (∏' n : ℕ, (1 - q ^ (n + 1))) ^ (24 : Nat)

@[simp] lemma deltaEulerProduct_zero : deltaEulerProduct 0 = 1 := by
  simp [deltaEulerProduct]

@[simp] lemma Delta_cusp_eq_mul_deltaEulerProduct (q : ℂ) :
    Delta_cusp q = q * deltaEulerProduct q := by
  simp [Delta_cusp, deltaEulerProduct]

lemma inv_mul_Delta_cusp_eq_deltaEulerProduct (q : ℂ) (hq0 : q ≠ 0) :
    q⁻¹ * Delta_cusp q = deltaEulerProduct q := by
  calc
    q⁻¹ * Delta_cusp q = q⁻¹ * (q * deltaEulerProduct q) := by
      rw [Delta_cusp_eq_mul_deltaEulerProduct]
    _ = (q⁻¹ * q) * deltaEulerProduct q := by ring
    _ = deltaEulerProduct q := by simp [hq0]

lemma mul_inv_Delta_cusp_eq_deltaEulerProduct (q : ℂ) (hq0 : q ≠ 0) :
    q⁻¹ * Delta_cusp q = deltaEulerProduct q :=
  inv_mul_Delta_cusp_eq_deltaEulerProduct q hq0

private lemma one_sub_pow_ne_zero_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    (1 : ℂ) - q ^ (n + 1) ≠ 0 := by
  refine sub_ne_zero.mpr ?_
  intro hEq
  have hnorm' : (1 : ℝ) = ‖q‖ ^ (n + 1) := by
    have := congrArg norm hEq
    simpa [norm_pow] using this
  have hnorm : ‖q‖ ^ (n + 1) = (1 : ℝ) := hnorm'.symm
  have hlt : ‖q‖ ^ (n + 1) < (1 : ℝ) :=
    pow_lt_one₀ (norm_nonneg q) hq (n := n + 1) (by exact Nat.succ_ne_zero n)
  exact (ne_of_lt hlt) hnorm

lemma deltaEulerProduct_ne_zero_of_norm_lt_one
    {q : ℂ} (hq : ‖q‖ < 1) :
    deltaEulerProduct q ≠ 0 := by
  have hs : Summable (fun n : ℕ => ‖-(q ^ (n + 1))‖) := by
    have hs' : Summable (fun n : ℕ => ‖q‖ ^ (n + 1)) := by
      have hgeom : Summable (fun n : ℕ => (‖q‖ : ℝ) ^ n) :=
        summable_geometric_of_lt_one (norm_nonneg q) hq
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using (hgeom.mul_left ‖q‖)
    simpa [norm_neg, norm_pow] using hs'
  have hprod : (∏' n : ℕ, (1 - q ^ (n + 1))) ≠ 0 := by
    refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(q ^ (n + 1))) ?_ hs
    intro n
    simpa [sub_eq_add_neg] using one_sub_pow_ne_zero_of_norm_lt_one (q := q) hq n
  simpa [deltaEulerProduct] using pow_ne_zero (24 : Nat) hprod

lemma deltaEulerProduct_ne_zero_of_norm_lt_one_of_ne_zero
    {q : ℂ} (hq : ‖q‖ < 1) (_hq0 : q ≠ 0) :
    deltaEulerProduct q ≠ 0 := by
  exact deltaEulerProduct_ne_zero_of_norm_lt_one (q := q) hq

lemma deltaEulerProduct_ne_zero_of_eq_q (τ : ℍ) :
    deltaEulerProduct (q τ) ≠ 0 := by
  exact deltaEulerProduct_ne_zero_of_norm_lt_one_of_ne_zero (norm_q_lt_one τ) (q_ne_zero τ)

private lemma hasProdUniformlyOn_deltaFactors_closedBall_half :
    HasProdUniformlyOn
      (fun n : ℕ => fun w : ℂ => (1 - w ^ (n + 1)))
      (fun w : ℂ => ∏' n : ℕ, (1 - w ^ (n + 1)))
      {Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)} := by
  let u : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 1)
  have hu : Summable u := by
    have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by positivity) (by norm_num)
    simpa [u, pow_succ, mul_assoc, mul_left_comm, mul_comm] using (hgeom.mul_left (1 / 2 : ℝ))
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ),
          ‖-(w ^ (n + 1))‖ ≤ u n := by
    refine Filter.Eventually.of_forall ?_
    intro n w hw
    have hnorm : ‖w‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm] using hw
    have hpow : ‖w‖ ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      exact pow_le_pow_left₀ (norm_nonneg w) hnorm (n + 1)
    simpa [u, norm_neg, norm_pow] using hpow
  have hcts :
      ∀ n : ℕ, ContinuousOn (fun w : ℂ => -(w ^ (n + 1)))
        (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
    intro n
    exact (continuous_neg.comp (continuous_pow (n + 1))).continuousOn
  have hprod :=
    Summable.hasProdUniformlyOn_nat_one_add
      (K := Metric.closedBall (0 : ℂ) (1 / 2 : ℝ))
      (f := fun n : ℕ => fun w : ℂ => -(w ^ (n + 1)))
      (u := u)
      (isCompact_closedBall (x := (0 : ℂ)) (r := (1 / 2 : ℝ)))
      hu hbound hcts
  simpa [sub_eq_add_neg] using hprod

private lemma continuousOn_tprod_deltaFactors_closedBall_half :
    ContinuousOn (fun w : ℂ => ∏' n : ℕ, (1 - w ^ (n + 1)))
      (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
  have hprod : TendstoUniformlyOn
      (fun N : ℕ => fun w : ℂ => ∏ n ∈ Finset.range N, (1 - w ^ (n + 1)))
      (fun w : ℂ => ∏' n : ℕ, (1 - w ^ (n + 1)))
      atTop
      (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) :=
    hasProdUniformlyOn_deltaFactors_closedBall_half.tendstoUniformlyOn_finsetRange (by simp)
  have hcts :
      ∀ᶠ N : ℕ in atTop,
        ContinuousOn
          (fun w : ℂ => ∏ n ∈ Finset.range N, (1 - w ^ (n + 1)))
          (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    exact (continuous_finset_prod (Finset.range N)
      (fun n _ => (continuous_const.sub (continuous_pow (n + 1))))).continuousOn
  exact hprod.continuousOn hcts

lemma tendsto_deltaEulerProduct_at_zero :
    Tendsto deltaEulerProduct (nhds (0 : ℂ)) (nhds (1 : ℂ)) := by
  have hcont :
      ContinuousAt (fun w : ℂ => ∏' n : ℕ, (1 - w ^ (n + 1))) (0 : ℂ) := by
    refine continuousOn_tprod_deltaFactors_closedBall_half.continuousAt ?_
    exact Metric.closedBall_mem_nhds (x := (0 : ℂ)) (by positivity)
  have hbase :
      (fun w : ℂ => ∏' n : ℕ, (1 - w ^ (n + 1))) 0 = (1 : ℂ) := by
    simp
  have hmain :
      Tendsto (fun w : ℂ => ∏' n : ℕ, (1 - w ^ (n + 1)))
        (nhds (0 : ℂ)) (nhds (1 : ℂ)) := by
    simpa [hbase] using hcont.tendsto
  have hpow :
      Tendsto (fun z : ℂ => z ^ (24 : Nat)) (nhds (1 : ℂ)) (nhds (1 : ℂ)) := by
    simpa using ((continuous_pow (24 : Nat)).continuousAt.tendsto : Tendsto (fun z : ℂ => z ^ (24 : Nat))
      (nhds (1 : ℂ)) (nhds ((1 : ℂ) ^ (24 : Nat))))
  simpa [deltaEulerProduct] using hpow.comp hmain

lemma tendsto_deltaEulerProduct_at_zero_within_punctured :
    Tendsto deltaEulerProduct (nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ) (nhds (1 : ℂ)) :=
  tendsto_deltaEulerProduct_at_zero.mono_left nhdsWithin_le_nhds

lemma tendsto_deltaEulerProduct_q_atImInfty :
    Tendsto (fun τ : ℍ => deltaEulerProduct (q τ))
      UpperHalfPlane.atImInfty (nhds (1 : ℂ)) := by
  exact tendsto_deltaEulerProduct_at_zero_within_punctured.comp tendsto_q_atImInfty

lemma Delta_eq_q_mul_deltaEulerProduct (τ : ℍ) :
    Delta τ = q τ * deltaEulerProduct (q τ) := by
  calc
    Delta τ = Delta_cusp (q τ) := Delta_eq_Delta_cusp (τ := τ)
    _ = q τ * deltaEulerProduct (q τ) := Delta_cusp_eq_mul_deltaEulerProduct (q τ)

lemma deltaEulerProduct_eq_inv_mul_Delta_of_eq_q (τ : ℍ) :
    deltaEulerProduct (q τ) = (q τ)⁻¹ * Delta τ := by
  calc
    deltaEulerProduct (q τ) = (q τ)⁻¹ * Delta_cusp (q τ) := by
      rw [inv_mul_Delta_cusp_eq_deltaEulerProduct (q τ) (q_ne_zero τ)]
    _ = (q τ)⁻¹ * Delta τ := by
      rw [Delta_eq_Delta_cusp (τ := τ)]

lemma deltaEulerProduct_mul_q_eq_Delta (τ : ℍ) :
    (q τ) * deltaEulerProduct (q τ) = Delta τ := by
  simpa [mul_comm] using (Delta_eq_q_mul_deltaEulerProduct (τ := τ)).symm

lemma kleinBfunExt_eq_1728_mul_deltaEulerProduct_zero :
    kleinBfunExt 0 = (1728 : ℂ) * deltaEulerProduct 0 := by
  simp [kleinBfunExt_zero]

lemma kleinBfunExt_sub_1728_mul_deltaEulerProduct_zero :
    kleinBfunExt 0 - (1728 : ℂ) * deltaEulerProduct 0 = 0 := by
  simp [kleinBfunExt_eq_1728_mul_deltaEulerProduct_zero]

/-- Normalized Euler-product ratio for the cusp contract target. -/
noncomputable def kleinEulerRatio (q : ℂ) : ℂ :=
  kleinBfunExt q / ((1728 : ℂ) * deltaEulerProduct q)

lemma kleinEulerRatio_zero : kleinEulerRatio 0 = 1 := by
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  have hden : ((1728 : ℂ) * deltaEulerProduct 0) ≠ 0 := by
    simp [deltaEulerProduct_zero, h1728]
  apply (div_eq_iff hden).2
  simpa [kleinEulerRatio, mul_assoc] using kleinBfunExt_eq_1728_mul_deltaEulerProduct_zero

lemma Delta_cusp_zero : Delta_cusp 0 = 0 := by
  simp [Delta_cusp]

lemma deltaEulerProduct_zero_ne_zero : deltaEulerProduct 0 ≠ 0 := by
  simp [deltaEulerProduct_zero]

lemma hasDerivAt_kleinDfun_zero : HasDerivAt kleinDfun (1728 : ℂ) 0 := by
  simpa [powerSeriesFml_coeff, kleinDps_coeff_one] using
    (HasFPowerSeriesAt.hasDerivAt (h := hasFPowerSeriesAt_kleinDfun))

lemma deriv_kleinDfun_zero : deriv kleinDfun 0 = (1728 : ℂ) := by
  exact hasDerivAt_kleinDfun_zero.deriv

lemma kleinDfun_sub_linear_isLittleO :
    (fun h : ℂ => kleinDfun h - (1728 : ℂ) * h) =o[nhds (0 : ℂ)] fun h => h := by
  have hLittle :
      (fun h : ℂ => kleinDfun (0 + h) - kleinDfun 0 - h • (1728 : ℂ)) =o[nhds (0 : ℂ)] fun h => h :=
    (hasDerivAt_iff_isLittleO_nhds_zero).1 hasDerivAt_kleinDfun_zero
  simpa [kleinDfun_zero, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hLittle

lemma tendsto_kleinDfun_div_at_zero :
    Tendsto (fun h : ℂ => kleinDfun h / h)
      (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (1728 : ℂ)) := by
  have hLittleWithin :
      (fun h : ℂ => kleinDfun h - (1728 : ℂ) * h) =o[nhdsWithin (0 : ℂ) ({0}ᶜ)] fun h => h :=
    kleinDfun_sub_linear_isLittleO.mono nhdsWithin_le_nhds
  have hQuot :
      Tendsto (fun h : ℂ => (kleinDfun h - (1728 : ℂ) * h) / h)
        (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (0 : ℂ)) :=
    (Asymptotics.isLittleO_iff_tendsto
      (l := nhdsWithin (0 : ℂ) ({0}ᶜ))
      (f := fun h : ℂ => kleinDfun h - (1728 : ℂ) * h)
      (g := fun h : ℂ => h)
      (fun h hh => by simp [hh, kleinDfun_zero])).1 hLittleWithin
  have hNe : ∀ᶠ h : ℂ in nhdsWithin (0 : ℂ) ({0}ᶜ), h ≠ 0 := self_mem_nhdsWithin
  have hEq :
      (fun h : ℂ => kleinDfun h / h) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        (fun h : ℂ => (kleinDfun h - (1728 : ℂ) * h) / h + (1728 : ℂ)) := by
    filter_upwards [hNe] with h hh
    field_simp [hh]
    ring
  have hSum :
      Tendsto (fun h : ℂ => (kleinDfun h - (1728 : ℂ) * h) / h + (1728 : ℂ))
        (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds (1728 : ℂ)) := by
    simpa using (hQuot.add tendsto_const_nhds)
  exact (tendsto_congr' hEq).2 hSum

lemma tendsto_kleinDfun_div_q_atImInfty :
    Tendsto (fun τ : ℍ => kleinDfun (q τ) / q τ)
      UpperHalfPlane.atImInfty (nhds (1728 : ℂ)) := by
  exact tendsto_kleinDfun_div_at_zero.comp tendsto_q_atImInfty

lemma tendsto_kleinEulerRatio_atImInfty :
    Tendsto (fun τ : ℍ => kleinEulerRatio (q τ))
      UpperHalfPlane.atImInfty (nhds (1 : ℂ)) := by
  have hnumInv :
      Tendsto (fun τ : ℍ => (q τ)⁻¹ * kleinDfun (q τ))
        UpperHalfPlane.atImInfty (nhds (1728 : ℂ)) := by
    have hEq :
        (fun τ : ℍ => (q τ)⁻¹ * kleinDfun (q τ))
          =ᶠ[UpperHalfPlane.atImInfty]
            (fun τ : ℍ => kleinDfun (q τ) / q τ) := by
      refine Filter.Eventually.of_forall ?_
      intro τ
      field_simp [q_ne_zero τ]
    exact (tendsto_congr' hEq).2 tendsto_kleinDfun_div_q_atImInfty
  have hden :
      Tendsto (fun τ : ℍ => (1728 : ℂ) * deltaEulerProduct (q τ))
        UpperHalfPlane.atImInfty (nhds (1728 : ℂ)) := by
    have h1728 : (1728 : ℂ) * (1 : ℂ) = (1728 : ℂ) := by ring
    simpa [h1728] using (tendsto_const_nhds.mul tendsto_deltaEulerProduct_q_atImInfty)
  have hquot :
      Tendsto
        (fun τ : ℍ =>
          ((q τ)⁻¹ * kleinDfun (q τ)) / ((1728 : ℂ) * deltaEulerProduct (q τ)))
        UpperHalfPlane.atImInfty (nhds (1 : ℂ)) := by
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    simpa using (hnumInv.div hden h1728)
  have hEq :
      (fun τ : ℍ => kleinEulerRatio (q τ)) =ᶠ[UpperHalfPlane.atImInfty]
        (fun τ : ℍ =>
          ((q τ)⁻¹ * kleinDfun (q τ)) / ((1728 : ℂ) * deltaEulerProduct (q τ))) := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    change kleinBfunExt (q τ) / ((1728 : ℂ) * deltaEulerProduct (q τ)) =
      ((q τ)⁻¹ * kleinDfun (q τ)) / ((1728 : ℂ) * deltaEulerProduct (q τ))
    rw [kleinBfunExt_eq_div (q := q τ) (q_ne_zero τ)]
  exact (tendsto_congr' hEq).2 hquot

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eulerProduct :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔
      (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
        kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q) := by
  constructor
  · intro h q hq hq0
    calc
      kleinBfunExt q = (1728 : ℂ) * q⁻¹ * Delta_cusp q := h q hq hq0
      _ = (1728 : ℂ) * (q⁻¹ * Delta_cusp q) := by ring
      _ = (1728 : ℂ) * deltaEulerProduct q := by
            rw [inv_mul_Delta_cusp_eq_deltaEulerProduct q hq0]
  · intro h q hq hq0
    calc
      kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q := h q hq hq0
      _ = (1728 : ℂ) * (q⁻¹ * Delta_cusp q) := by
            rw [inv_mul_Delta_cusp_eq_deltaEulerProduct q hq0]
      _ = (1728 : ℂ) * q⁻¹ * Delta_cusp q := by ring

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_kleinEulerRatio_eq_one :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔
      (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1) := by
  constructor
  · intro h q hq hq0
    have hMain : kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q := by
      exact (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eulerProduct.1 h) q hq hq0
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    have hden : ((1728 : ℂ) * deltaEulerProduct q) ≠ 0 := by
      exact mul_ne_zero h1728 (deltaEulerProduct_ne_zero_of_norm_lt_one (q := q) hq)
    apply (div_eq_iff hden).2
    simpa [kleinEulerRatio, mul_assoc] using hMain
  · intro h
    refine (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eulerProduct).2 ?_
    intro q hq hq0
    have hRatio : kleinEulerRatio q = 1 := h q hq hq0
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    have hden : ((1728 : ℂ) * deltaEulerProduct q) ≠ 0 := by
      exact mul_ne_zero h1728 (deltaEulerProduct_ne_zero_of_norm_lt_one (q := q) hq)
    have hMain : kleinBfunExt q = 1 * ((1728 : ℂ) * deltaEulerProduct q) := by
      exact (div_eq_iff hden).1 (by simpa [kleinEulerRatio] using hRatio)
    simpa using hMain

theorem kleinBfunExtDeltaIdentityCusp_iff_eulerProduct :
    KleinBfunExtDeltaIdentityCusp ↔
      (∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) := by
  constructor
  · intro h τ
    calc
      kleinBfunExt (q τ) = (1728 : ℂ) * (q τ)⁻¹ * Delta_cusp (q τ) := h τ
      _ = (1728 : ℂ) * ((q τ)⁻¹ * Delta_cusp (q τ)) := by ring
      _ = (1728 : ℂ) * deltaEulerProduct (q τ) := by
            rw [inv_mul_Delta_cusp_eq_deltaEulerProduct (q τ) (q_ne_zero τ)]
  · intro h τ
    calc
      kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ) := h τ
      _ = (1728 : ℂ) * ((q τ)⁻¹ * Delta_cusp (q τ)) := by
            rw [inv_mul_Delta_cusp_eq_deltaEulerProduct (q τ) (q_ne_zero τ)]
      _ = (1728 : ℂ) * (q τ)⁻¹ * Delta_cusp (q τ) := by ring

theorem kleinBfunExtDeltaIdentityCusp_iff_kleinEulerRatio_eq_one :
    KleinBfunExtDeltaIdentityCusp ↔
      (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) := by
  constructor
  · intro h τ
    have hPunct : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
      (kleinBfunExtDeltaIdentityCusp_iff_puncturedUnitDisk).1 h
    exact (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_kleinEulerRatio_eq_one.1 hPunct)
      (q τ) (norm_q_lt_one τ) (q_ne_zero τ)
  · intro h
    refine (kleinBfunExtDeltaIdentityCusp_iff_puncturedUnitDisk).2 ?_
    refine (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_kleinEulerRatio_eq_one).2 ?_
    intro w hw hw0
    let τ : ℍ :=
      ⟨Function.Periodic.invQParam 1 w,
        Function.Periodic.im_invQParam_pos_of_norm_lt_one Real.zero_lt_one hw hw0⟩
    have hwτ : q τ = w := by
      dsimp [q, τ]
      simpa using (Function.Periodic.qParam_right_inv (h := (1 : ℝ)) one_ne_zero hw0)
    simpa [hwτ] using h τ

theorem kleinEulerRatio_eq_one_iff_discriminant_punctured {q : ℂ}
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    kleinEulerRatio q = 1 ↔ kleinDfun q = (1728 : ℂ) * Delta_cusp q := by
  constructor
  · intro hRatio
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    have hdenRatio : ((1728 : ℂ) * deltaEulerProduct q) ≠ 0 := by
      exact mul_ne_zero h1728 (deltaEulerProduct_ne_zero_of_norm_lt_one (q := q) hq)
    have hBfun : kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q := by
      have : kleinBfunExt q = 1 * ((1728 : ℂ) * deltaEulerProduct q) := by
        exact (div_eq_iff hdenRatio).1 (by simpa [kleinEulerRatio] using hRatio)
      simpa using this
    calc
      kleinDfun q = q * kleinBfunExt q := by
        simpa using (kleinDfun_eq_mul_kleinBfunExt (q := q) hq0)
      _ = q * ((1728 : ℂ) * deltaEulerProduct q) := by rw [hBfun]
      _ = (1728 : ℂ) * (q * deltaEulerProduct q) := by ring
      _ = (1728 : ℂ) * Delta_cusp q := by rw [Delta_cusp_eq_mul_deltaEulerProduct]
  · intro hDisc
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    have hBfun : kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q := by
      calc
        kleinBfunExt q = q⁻¹ * kleinDfun q := by
          exact kleinBfunExt_eq_div (q := q) hq0
        _ = q⁻¹ * ((1728 : ℂ) * Delta_cusp q) := by rw [hDisc]
        _ = (1728 : ℂ) * (q⁻¹ * Delta_cusp q) := by ring
        _ = (1728 : ℂ) * deltaEulerProduct q := by
          rw [inv_mul_Delta_cusp_eq_deltaEulerProduct q hq0]
    have hdenRatio : ((1728 : ℂ) * deltaEulerProduct q) ≠ 0 := by
      exact mul_ne_zero h1728 (deltaEulerProduct_ne_zero_of_norm_lt_one (q := q) hq)
    exact (div_eq_iff hdenRatio).2 (by simpa [kleinEulerRatio] using hBfun)

theorem kleinEulerRatio_eq_one_iff_discriminant_at_cusp (τ : ℍ) :
    kleinEulerRatio (q τ) = 1 ↔ kleinDenom τ = (1728 : ℂ) * Delta τ := by
  have hq0 : q τ ≠ 0 := q_ne_zero τ
  constructor
  · intro hRatio
    have hDiscPunct :
        kleinDfun (q τ) = (1728 : ℂ) * Delta_cusp (q τ) :=
      (kleinEulerRatio_eq_one_iff_discriminant_punctured
        (q := q τ) (norm_q_lt_one τ) hq0).1 hRatio
    calc
      kleinDenom τ = kleinDfun (q τ) := kleinDenom_eq_kleinDfun (τ := τ)
      _ = (1728 : ℂ) * Delta_cusp (q τ) := hDiscPunct
      _ = (1728 : ℂ) * Delta τ := by rw [Delta_eq_Delta_cusp (τ := τ)]
  · intro hDisc
    have hDiscPunct :
        kleinDfun (q τ) = (1728 : ℂ) * Delta_cusp (q τ) := by
      calc
        kleinDfun (q τ) = kleinDenom τ := (kleinDenom_eq_kleinDfun (τ := τ)).symm
        _ = (1728 : ℂ) * Delta τ := hDisc
        _ = (1728 : ℂ) * Delta_cusp (q τ) := by rw [Delta_eq_Delta_cusp (τ := τ)]
    exact (kleinEulerRatio_eq_one_iff_discriminant_punctured
      (q := q τ) (norm_q_lt_one τ) hq0).2 hDiscPunct

theorem kleinEulerRatio_eq_one_iff_eisensteinEta_at_cusp (τ : ℍ) :
    kleinEulerRatio (q τ) = 1 ↔
      (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat) := by
  simpa [kleinDenom, Delta] using (kleinEulerRatio_eq_one_iff_discriminant_at_cusp (τ := τ))

theorem kleinEulerRatioCusp_iff_eisensteinEtaIdentity_pointwise :
    (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) ↔
      (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
        (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
  constructor
  · intro hRatio τ
    exact (kleinEulerRatio_eq_one_iff_eisensteinEta_at_cusp (τ := τ)).1 (hRatio τ)
  · intro hEta τ
    exact (kleinEulerRatio_eq_one_iff_eisensteinEta_at_cusp (τ := τ)).2 (hEta τ)

theorem kleinEulerRatio_at_cusp_eq_div (τ : ℍ) :
    kleinEulerRatio (q τ) = kleinDenom τ / ((1728 : ℂ) * Delta τ) := by
  have hq0 : q τ ≠ 0 := q_ne_zero τ
  have hqinv : (q τ)⁻¹ ≠ 0 := inv_ne_zero hq0
  calc
    kleinEulerRatio (q τ)
        = kleinBfunExt (q τ) / ((1728 : ℂ) * deltaEulerProduct (q τ)) := rfl
    _ = ((q τ)⁻¹ * kleinDenom τ) / ((1728 : ℂ) * deltaEulerProduct (q τ)) := by
          rw [kleinBfunExt_eq_div (q := q τ) hq0, kleinDenom_eq_kleinDfun (τ := τ)]
    _ = ((q τ)⁻¹ * kleinDenom τ) / ((1728 : ℂ) * ((q τ)⁻¹ * Delta τ)) := by
          rw [deltaEulerProduct_eq_inv_mul_Delta_of_eq_q (τ := τ)]
    _ = ((q τ)⁻¹ * kleinDenom τ) / ((q τ)⁻¹ * ((1728 : ℂ) * Delta τ)) := by
          ring_nf
    _ = kleinDenom τ / ((1728 : ℂ) * Delta τ) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (mul_div_mul_left (kleinDenom τ) ((1728 : ℂ) * Delta τ) hqinv)

lemma tendsto_kleinDenom_div_Delta_atImInfty :
    Tendsto (fun τ : ℍ => kleinDenom τ / Delta τ)
      UpperHalfPlane.atImInfty (nhds (1728 : ℂ)) := by
  have hbase :
      Tendsto (fun τ : ℍ => kleinDenom τ / ((1728 : ℂ) * Delta τ))
        UpperHalfPlane.atImInfty (nhds (1 : ℂ)) := by
    have hEq :
        (fun τ : ℍ => kleinEulerRatio (q τ)) =ᶠ[UpperHalfPlane.atImInfty]
          (fun τ : ℍ => kleinDenom τ / ((1728 : ℂ) * Delta τ)) := by
      exact Filter.Eventually.of_forall (fun τ => kleinEulerRatio_at_cusp_eq_div (τ := τ))
    exact (tendsto_congr' hEq).1 tendsto_kleinEulerRatio_atImInfty
  have hscaled :
      Tendsto (fun τ : ℍ => (1728 : ℂ) * (kleinDenom τ / ((1728 : ℂ) * Delta τ)))
        UpperHalfPlane.atImInfty (nhds (1728 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hbase)
  have hEq :
      (fun τ : ℍ => (1728 : ℂ) * (kleinDenom τ / ((1728 : ℂ) * Delta τ)))
        =ᶠ[UpperHalfPlane.atImInfty] (fun τ : ℍ => kleinDenom τ / Delta τ) := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    have hDelta : Delta τ ≠ 0 := Delta_ne_zero τ
    field_simp [h1728, hDelta, mul_assoc, mul_comm, mul_left_comm]
  exact (tendsto_congr' hEq).1 hscaled

theorem kleinEulerRatioCusp_eq_one_iff_kleinDenom_div_Delta_eq_1728 :
    (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) ↔
      (∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) := by
  constructor
  · intro hRatio τ
    have hDisc : kleinDenom τ = (1728 : ℂ) * Delta τ :=
      (kleinEulerRatio_eq_one_iff_discriminant_at_cusp (τ := τ)).1 (hRatio τ)
    have hDelta : Delta τ ≠ 0 := Delta_ne_zero τ
    exact (div_eq_iff hDelta).2 (by simpa [mul_comm] using hDisc)
  · intro hDiv τ
    have hDelta : Delta τ ≠ 0 := Delta_ne_zero τ
    have hDisc : kleinDenom τ = (1728 : ℂ) * Delta τ := by
      exact (div_eq_iff hDelta).1 (by simpa [mul_comm] using hDiv τ)
    exact (kleinEulerRatio_eq_one_iff_discriminant_at_cusp (τ := τ)).2 hDisc

theorem kleinDiscriminantIdentity_iff_q_mul_eulerProduct :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (q τ) * deltaEulerProduct (q τ)) := by
  constructor
  · intro hDisc τ
    calc
      kleinDenom τ = (1728 : ℂ) * Delta τ := hDisc τ
      _ = (1728 : ℂ) * (q τ * deltaEulerProduct (q τ)) := by
            rw [Delta_eq_q_mul_deltaEulerProduct]
      _ = (1728 : ℂ) * (q τ) * deltaEulerProduct (q τ) := by ring
  · intro hEuler τ
    calc
      kleinDenom τ = (1728 : ℂ) * (q τ) * deltaEulerProduct (q τ) := hEuler τ
      _ = (1728 : ℂ) * (q τ * deltaEulerProduct (q τ)) := by ring
      _ = (1728 : ℂ) * Delta τ := by
            rw [Delta_eq_q_mul_deltaEulerProduct]

theorem kleinDiscriminantIdentity_iff_eulerProductCusp :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) := by
  calc
    KleinDiscriminantIdentity ↔ KleinBfunExtDeltaIdentityCusp := by
      exact kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityCusp
    _ ↔ (∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) := by
      exact kleinBfunExtDeltaIdentityCusp_iff_eulerProduct

theorem kleinDenom_ne_zero_global_of_eulerProductCusp
    (hEulerCusp : ∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  have hCusp : KleinBfunExtDeltaIdentityCusp :=
    (kleinBfunExtDeltaIdentityCusp_iff_eulerProduct).2 hEulerCusp
  exact kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityCusp hCusp

theorem kleinDiscriminantIdentity_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    KleinDiscriminantIdentity := by
  exact (kleinDiscriminantIdentity_iff_eisensteinEtaIdentity).2 hEta

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  exact (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eisensteinEtaIdentity).2 hEta

theorem kleinBfunExtDeltaIdentityCusp_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    KleinBfunExtDeltaIdentityCusp := by
  exact (kleinBfunExtDeltaIdentityCusp_iff_eisensteinEtaIdentity).2 hEta

theorem kleinDenom_ne_zero_global_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  exact kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityCusp
    (kleinBfunExtDeltaIdentityCusp_of_eisensteinEtaIdentity hEta)

theorem eisensteinEtaIdentity_iff_eulerProductCusp :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      (∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) := by
  calc
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
        (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔ KleinBfunExtDeltaIdentityCusp := by
      exact (kleinBfunExtDeltaIdentityCusp_iff_eisensteinEtaIdentity).symm
    _ ↔ (∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) := by
      exact kleinBfunExtDeltaIdentityCusp_iff_eulerProduct

theorem eisensteinEtaIdentity_of_eulerProductCusp
    (hEulerCusp : ∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) := by
  exact (eisensteinEtaIdentity_iff_eulerProductCusp).2 hEulerCusp

theorem eulerProductCusp_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ) := by
  exact (eisensteinEtaIdentity_iff_eulerProductCusp).1 hEta

theorem eisensteinEtaIdentity_iff_eulerProductPunctured :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
        kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q) := by
  calc
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
        (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔ KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
      exact (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eisensteinEtaIdentity).symm
    _ ↔ (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
      kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q) := by
      exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eulerProduct

theorem eisensteinEtaIdentity_of_eulerProductPunctured
    (hEuler : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
      kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) := by
  exact (eisensteinEtaIdentity_iff_eulerProductPunctured).2 hEuler

theorem eulerProductPunctured_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
      kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q := by
  exact (eisensteinEtaIdentity_iff_eulerProductPunctured).1 hEta

theorem eisensteinEtaIdentity_iff_kleinEulerRatioCusp :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) := by
  calc
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
        (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔ KleinBfunExtDeltaIdentityCusp := by
      exact (kleinBfunExtDeltaIdentityCusp_iff_eisensteinEtaIdentity).symm
    _ ↔ (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) := by
      exact kleinBfunExtDeltaIdentityCusp_iff_kleinEulerRatio_eq_one

theorem eisensteinEtaIdentity_of_kleinEulerRatioCusp
    (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) := by
  exact (eisensteinEtaIdentity_iff_kleinEulerRatioCusp).2 hRatio

theorem kleinEulerRatioCusp_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ τ : ℍ, kleinEulerRatio (q τ) = 1 := by
  exact (eisensteinEtaIdentity_iff_kleinEulerRatioCusp).1 hEta

theorem eisensteinEtaIdentity_iff_kleinEulerRatioPunctured :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1) := by
  calc
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
        (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔ KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
      exact (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eisensteinEtaIdentity).symm
    _ ↔ (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1) := by
      exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_kleinEulerRatio_eq_one

theorem eisensteinEtaIdentity_of_kleinEulerRatioPunctured
    (hRatio : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) := by
  exact (eisensteinEtaIdentity_iff_kleinEulerRatioPunctured).2 hRatio

theorem kleinEulerRatioPunctured_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1 := by
  exact (eisensteinEtaIdentity_iff_kleinEulerRatioPunctured).1 hEta

theorem kleinDiscriminantIdentity_of_kleinEulerRatioCusp
    (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    KleinDiscriminantIdentity := by
  exact kleinDiscriminantIdentity_of_eisensteinEtaIdentity
    (eisensteinEtaIdentity_of_kleinEulerRatioCusp hRatio)

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_kleinEulerRatioCusp
    (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_eisensteinEtaIdentity
    (eisensteinEtaIdentity_of_kleinEulerRatioCusp hRatio)

theorem kleinDenom_ne_zero_global_of_kleinEulerRatioCusp
    (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  exact kleinDenom_ne_zero_global_of_eisensteinEtaIdentity
    (eisensteinEtaIdentity_of_kleinEulerRatioCusp hRatio)

theorem kleinEulerRatioCusp_of_kleinDenom_div_Delta_eq_1728
    (hDiv : ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :
    ∀ τ : ℍ, kleinEulerRatio (q τ) = 1 := by
  exact (kleinEulerRatioCusp_eq_one_iff_kleinDenom_div_Delta_eq_1728).2 hDiv

theorem kleinDenom_div_Delta_eq_1728_of_kleinEulerRatioCusp
    (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) := by
  exact (kleinEulerRatioCusp_eq_one_iff_kleinDenom_div_Delta_eq_1728).1 hRatio

theorem kleinDiscriminantIdentity_of_kleinDenom_div_Delta_eq_1728
    (hDiv : ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :
    KleinDiscriminantIdentity := by
  exact kleinDiscriminantIdentity_of_kleinEulerRatioCusp
    (kleinEulerRatioCusp_of_kleinDenom_div_Delta_eq_1728 hDiv)

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_kleinDenom_div_Delta_eq_1728
    (hDiv : ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_kleinEulerRatioCusp
    (kleinEulerRatioCusp_of_kleinDenom_div_Delta_eq_1728 hDiv)

theorem kleinDenom_div_Delta_eq_1728_of_kleinDiscriminantIdentity
    (hDisc : KleinDiscriminantIdentity) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) := by
  intro τ
  have hDelta : Delta τ ≠ 0 := Delta_ne_zero τ
  exact (div_eq_iff hDelta).2 (by simpa [mul_comm] using hDisc τ)

theorem kleinDiscriminantIdentity_iff_kleinDenom_div_Delta_eq_1728 :
    KleinDiscriminantIdentity ↔ (∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) := by
  constructor
  · exact kleinDenom_div_Delta_eq_1728_of_kleinDiscriminantIdentity
  · exact kleinDiscriminantIdentity_of_kleinDenom_div_Delta_eq_1728

theorem kleinDenom_div_Delta_eq_1728_of_ratio_modularForm_weight_zero
    (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ)
    (τ0 : ℍ) (hAt : f τ0 = (1728 : ℂ)) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) := by
  rcases ModularFormClass.levelOne_weight_zero_const (f := f) with ⟨c, hc⟩
  have hc1728 : c = (1728 : ℂ) := by
    have hfc0 : f τ0 = c := by
      have hfc := congrArg (fun g : ℍ → ℂ => g τ0) hc
      simpa using hfc
    exact hfc0.symm.trans hAt
  intro τ
  calc
    kleinDenom τ / Delta τ = f τ := by simpa using (hRatio τ).symm
    _ = c := by
      have hfc := congrArg (fun g : ℍ → ℂ => g τ) hc
      simpa using hfc
    _ = (1728 : ℂ) := hc1728

theorem kleinDenom_div_Delta_eq_1728_of_ratio_modularForm_weight_zero_atImInfty
    (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) := by
  haveI : NeBot UpperHalfPlane.atImInfty := by
    rw [UpperHalfPlane.atImInfty]
    refine Filter.comap_neBot ?_
    intro t ht
    rcases mem_atTop_sets.mp ht with ⟨A, hA⟩
    let y : ℝ := max A 1
    have hy : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) (le_max_right A 1)
    let τ : ℍ := by
      refine ⟨(y : ℂ) * Complex.I, ?_⟩
      simp [y] at hy ⊢
    refine ⟨τ, ?_⟩
    have hyA : A ≤ y := le_max_left A 1
    have him : τ.im = y := by
      change Complex.im ((y : ℂ) * Complex.I) = y
      simp
    exact him ▸ (hA y hyA)
  rcases ModularFormClass.levelOne_weight_zero_const (f := f) with ⟨c, hc⟩
  have hlimF : Tendsto (fun τ : ℍ => f τ) UpperHalfPlane.atImInfty (nhds (1728 : ℂ)) := by
    have hEq :
        (fun τ : ℍ => f τ) =ᶠ[UpperHalfPlane.atImInfty]
          (fun τ : ℍ => kleinDenom τ / Delta τ) :=
      Filter.Eventually.of_forall hRatio
    exact (tendsto_congr' hEq).2 tendsto_kleinDenom_div_Delta_atImInfty
  have hlimConst1728 : Tendsto (fun _ : ℍ => c) UpperHalfPlane.atImInfty (nhds (1728 : ℂ)) := by
    have hEq :
        (fun τ : ℍ => f τ) =ᶠ[UpperHalfPlane.atImInfty]
          (fun _ : ℍ => c) := by
      refine Filter.Eventually.of_forall ?_
      intro τ
      have hfc := congrArg (fun g : ℍ → ℂ => g τ) hc
      simpa using hfc
    exact (tendsto_congr' hEq).1 hlimF
  have hc1728 : c = (1728 : ℂ) := by
    exact (tendsto_const_nhds_iff.mp hlimConst1728)
  intro τ
  calc
    kleinDenom τ / Delta τ = f τ := by simpa using (hRatio τ).symm
    _ = c := by
      have hfc := congrArg (fun g : ℍ → ℂ => g τ) hc
      simpa using hfc
    _ = (1728 : ℂ) := hc1728

theorem kleinDiscriminantIdentity_of_ratio_modularForm_weight_zero
    (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ)
    (τ0 : ℍ) (hAt : f τ0 = (1728 : ℂ)) :
    KleinDiscriminantIdentity := by
  exact kleinDiscriminantIdentity_of_kleinDenom_div_Delta_eq_1728
    (kleinDenom_div_Delta_eq_1728_of_ratio_modularForm_weight_zero f hRatio τ0 hAt)

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_ratio_modularForm_weight_zero
    (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ)
    (τ0 : ℍ) (hAt : f τ0 = (1728 : ℂ)) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_kleinDenom_div_Delta_eq_1728
    (kleinDenom_div_Delta_eq_1728_of_ratio_modularForm_weight_zero f hRatio τ0 hAt)

theorem kleinDiscriminantIdentity_of_ratio_modularForm_weight_zero_atImInfty
    (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) :
    KleinDiscriminantIdentity := by
  exact kleinDiscriminantIdentity_of_kleinDenom_div_Delta_eq_1728
    (kleinDenom_div_Delta_eq_1728_of_ratio_modularForm_weight_zero_atImInfty f hRatio)

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_ratio_modularForm_weight_zero_atImInfty
    (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_kleinDenom_div_Delta_eq_1728
    (kleinDenom_div_Delta_eq_1728_of_ratio_modularForm_weight_zero_atImInfty f hRatio)

theorem kleinDiscriminantIdentity_iff_exists_ratio_modularForm_weight_zero
    (τ0 : ℍ) :
    KleinDiscriminantIdentity ↔
      ∃ f : ModularForm Γ(1) 0,
        (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) := by
  constructor
  · intro hDisc
    refine ⟨ModularForm.const (Γ := Γ(1)) (1728 : ℂ), ?_, ?_⟩
    · intro τ
      have hDiv :
          ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) :=
        kleinDenom_div_Delta_eq_1728_of_kleinDiscriminantIdentity hDisc
      simpa using (hDiv τ).symm
    · simp
  · rintro ⟨f, hRatio, hAt⟩
    exact kleinDiscriminantIdentity_of_ratio_modularForm_weight_zero f hRatio τ0 hAt

theorem kleinDiscriminantIdentity_iff_exists_ratio_modularForm_weight_zero_no_anchor :
    KleinDiscriminantIdentity ↔
      ∃ f : ModularForm Γ(1) 0, ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ := by
  constructor
  · intro hDisc
    refine ⟨ModularForm.const (Γ := Γ(1)) (1728 : ℂ), ?_⟩
    intro τ
    have hDiv :
        ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) :=
      kleinDenom_div_Delta_eq_1728_of_kleinDiscriminantIdentity hDisc
    simpa using (hDiv τ).symm
  · rintro ⟨f, hRatio⟩
    exact kleinDiscriminantIdentity_of_ratio_modularForm_weight_zero_atImInfty f hRatio

theorem eisensteinEtaIdentity_iff_exists_ratio_modularForm_weight_zero
    (τ0 : ℍ) :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      ∃ f : ModularForm Γ(1) 0,
        (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) := by
  calc
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔ KleinDiscriminantIdentity := by
        exact (kleinDiscriminantIdentity_iff_eisensteinEtaIdentity).symm
    _ ↔ ∃ f : ModularForm Γ(1) 0,
      (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) := by
        exact kleinDiscriminantIdentity_iff_exists_ratio_modularForm_weight_zero τ0

end HeytingLean.Moonshine.Modular
