import HeytingLean.Moonshine.Modular.Delta
import HeytingLean.Moonshine.Modular.DeltaCusp
import HeytingLean.Moonshine.Modular.Eisenstein
import HeytingLean.Moonshine.Modular.JInvariant
import HeytingLean.Moonshine.Modular.JInvariantInvariance
import HeytingLean.Moonshine.Modular.KleinCuspFunction
import HeytingLean.Moonshine.Modular.KleinCuspLaurentBridge
import HeytingLean.Moonshine.Modular.KleinJ0LaurentEval
import HeytingLean.Moonshine.Modular.KleinJ0LaurentExpansion
import HeytingLean.Moonshine.Modular.Hauptmodul
import HeytingLean.Moonshine.Modular.LevelOneHauptmodulData
import HeytingLean.Moonshine.Modular.KleinDenominatorNonvanishing
import HeytingLean.Moonshine.Modular.KleinDenominatorGlobalReduction
import HeytingLean.Moonshine.Modular.KleinDenomCuspBridge
import HeytingLean.Moonshine.Modular.KleinBfunExtExplicitNonvanishing
import HeytingLean.Moonshine.Modular.KleinDenominatorCoefficients
import HeytingLean.Moonshine.Modular.KleinBfunExtTruncation
import HeytingLean.Moonshine.Modular.KleinDenominatorTailReduction
import HeytingLean.Moonshine.Modular.KleinDenominatorTailMajorant
import HeytingLean.Moonshine.Modular.KleinDiscriminantRoute
import HeytingLean.Moonshine.Modular.KleinDiscriminantIdentityProof
import HeytingLean.Moonshine.Modular.KleinRatioModularForm
import HeytingLean.Moonshine.Modular.KleinRatioWitness
import HeytingLean.Moonshine.Modular.FundamentalDomainQBounds
import HeytingLean.Moonshine.Modular.JSeries
import HeytingLean.Moonshine.Modular.QParam

set_option autoImplicit false

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

open scoped Topology
open Filter
open scoped MatrixGroups
open scoped CongruenceSubgroup

example (τ : ℍ) : eta τ ≠ 0 := eta_ne_zero τ
example (τ : ℍ) : Delta τ ≠ 0 := Delta_ne_zero τ
example (τ : ℍ) : Delta τ = Delta_cusp (q τ) := Delta_eq_Delta_cusp (τ := τ)
example (τ : ℍ) : Delta_cusp (q τ) ≠ 0 := Delta_cusp_ne_zero_of_eq_q (τ := τ)
example {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) : Delta_cusp q ≠ 0 :=
  Delta_cusp_ne_zero_of_norm_lt_one_of_ne_zero (q := q) hq hq0
example (τ : ℍ) : ‖q τ‖ < 1 := norm_q_lt_one τ

example (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion₁ E4).coeff m • (Function.Periodic.qParam 1 τ) ^ m) (E4 τ) :=
  hasSum_qExpansion₁ E4 τ

example (τ : ℍ) : kleinJ₀ τ = kleinJ τ - 744 := rfl

example (γ : SL(2, ℤ)) (τ : ℍ) : kleinJ (γ • τ) = kleinJ τ :=
  kleinJ_sl2_invariant (γ := γ) (τ := τ)

example (γ : SL(2, ℤ)) (τ : ℍ) : kleinJ₀ (γ • τ) = kleinJ₀ τ :=
  kleinJ₀_sl2_invariant (γ := γ) (τ := τ)

example (τ : ℍ) : kleinJ τ = kleinJ_cusp (Function.Periodic.qParam 1 τ) :=
  kleinJ_eq_kleinJ_cusp (τ := τ)

example (τ : ℍ) : kleinJ₀ τ = kleinJ₀_cusp (Function.Periodic.qParam 1 τ) :=
  kleinJ₀_eq_kleinJ₀_cusp (τ := τ)

example : (J_q.coeff (-1)) = (1 : ℂ) := coeff_J_q_neg1
example : (J_q.coeff 1) = (firstJCoeff : ℂ) := coeff_J_q_1

example : qExpansion₁ E4 = E4_q_expected := qExpansion₁_E4_eq_expected
example : qExpansion₁ E6 = E6_q_expected := qExpansion₁_E6_eq_expected

example :
    (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff (-1) = J_q.coeff (-1) := by
  simpa using (kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q).1

example :
    (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 0 = J_q.coeff 0 := by
  simpa using (kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q).2.1

example :
    (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 1 = J_q.coeff 1 := by
  simpa using (kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q).2.2.1

example :
    (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 2 = J_q.coeff 2 := by
  simpa using (kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q).2.2.2

example (q : ℂ) (hq : ‖q‖ < 1) :
    ((∑' n : ℕ, psTerm (qExpansion₁ E4) q n) * (∑' n : ℕ, psTerm (qExpansion₁ E4) q n)) =
      ∑' n : ℕ, psTerm ((qExpansion₁ E4) * (qExpansion₁ E4)) q n := by
  simpa using
    (tsum_mul_tsum_eq_tsum_coeff_mul (φ := qExpansion₁ E4) (ψ := qExpansion₁ E4) (q := q)
      (summable_norm_qExpansion₁_E4_term q hq) (summable_norm_qExpansion₁_E4_term q hq))

example :
    ∀ᶠ q in 𝓝 (0 : ℂ), q ≠ 0 → kleinJ₀_cusp q = kleinJ₀_qLaurent_eval q :=
  eventually_kleinJ₀_cusp_eq_kleinJ₀_qLaurent_eval

example :
    ∃ A : ℝ, ∀ τ : UpperHalfPlane, A < τ.im →
      kleinJ₀ τ =
        (q τ)⁻¹ + (firstJCoeff : ℂ) * (q τ)
          + (secondJCoeff : ℂ) * (q τ) ^ 2 + (q τ) ^ 3 * kleinA_tail_eval (q τ) :=
  exists_im_bound_kleinJ₀_eq_trunc

example : IsHauptmodulLike (⊤ : Subgroup SL2Z) kleinJ₀ :=
  kleinJ₀_isHauptmodulLike

example : IsHauptmodul (⊤ : Subgroup SL2Z) kleinJ₀ :=
  kleinJ₀_isHauptmodul

example (τ : ℍ) : kleinDenom τ ≠ 0 :=
  kleinJ₀_denominator_nonvanishing τ

example : IsHauptmodulLikeWithDenom (⊤ : Subgroup SL2Z) kleinJ₀ kleinDenom :=
  kleinJ₀_isHauptmodulLikeWithDenom

example : IsHauptmodulWithDenom (⊤ : Subgroup SL2Z) kleinJ₀ kleinDenom :=
  kleinJ₀_isHauptmodulWithDenom

example :
    ∃ A : ℝ, ∀ τ : ℍ, A < τ.im → (E4 τ) ^ 3 - (E6 τ) ^ 2 ≠ 0 :=
  exists_im_bound_kleinDenom_ne_zero


example (gamma : SL(2, ℤ)) (tau : ℍ) :
    kleinDenom (gamma • tau) = (denom gamma tau) ^ (12 : Nat) * kleinDenom tau :=
  kleinDenom_smul (γ := gamma) (τ := tau)

example {tau : ℍ} (htau : kleinDenom tau = 0) :
    ∃ xi : ℍ, xi ∈ ModularGroup.fd ∧ kleinDenom xi = 0 :=
  exists_mem_fd_of_kleinDenom_eq_zero (τ := tau) htau

example (τ : ℍ) : kleinDenom τ = q τ * kleinBfunExt (q τ) :=
  kleinDenom_eq_q_mul_kleinBfunExt (τ := τ)

example (τ : ℍ) : (kleinDenom τ ≠ 0 ↔ kleinBfunExt (q τ) ≠ 0) :=
  kleinDenom_ne_zero_iff_kleinBfunExt_ne_zero (τ := τ)

example {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) : (1 / 2 : ℝ) ≤ τ.im :=
  one_half_le_im_of_mem_fd (τ := τ) hτ

example {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) : Real.sqrt 3 / 2 ≤ τ.im :=
  sqrt_three_div_two_le_im_of_mem_fd (τ := τ) hτ

example {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) : ‖q τ‖ ≤ Real.exp (-Real.pi) :=
  norm_q_le_exp_neg_pi_of_mem_fd (τ := τ) hτ

example {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) : ‖q τ‖ ≤ Real.exp (-Real.pi * Real.sqrt 3) :=
  norm_q_le_exp_neg_pi_sqrt_three_of_mem_fd (τ := τ) hτ

example {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) : ‖q τ‖ ≤ (1 / 100 : ℝ) :=
  norm_q_le_one_div_hundred_of_mem_fd (τ := τ) hτ

example (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    kleinBfunExt q = ∑' n : ℕ, psTerm kleinBps q n :=
  kleinBfunExt_eq_tsum_psTerm_kleinBps (q := q) hq hq0

example : kleinDps.coeff 2 = (-41472 : ℂ) := kleinDps_coeff_two
example : kleinDps.coeff 3 = (435456 : ℂ) := kleinDps_coeff_three
example : kleinDps.coeff 4 = (-2543616 : ℂ) := kleinDps_coeff_four

example : kleinBps.coeff 1 = (-41472 : ℂ) := kleinBps_coeff_one
example : kleinBps.coeff 2 = (435456 : ℂ) := kleinBps_coeff_two
example : kleinBps.coeff 3 = (-2543616 : ℂ) := kleinBps_coeff_three

example (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    kleinBfunExt q =
      (1728 : ℂ)
        + (-41472 : ℂ) * q
        + (435456 : ℂ) * q ^ 2
        + (-2543616 : ℂ) * q ^ 3
        + q ^ 4 * kleinB_tail_eval q :=
  kleinBfunExt_eq_trunc_of_norm_lt_one_of_ne_zero (q := q) hq hq0

example (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    kleinBfunExt (q τ) =
      (1728 : ℂ)
        + (-41472 : ℂ) * (q τ)
        + (435456 : ℂ) * (q τ) ^ 2
        + (-2543616 : ℂ) * (q τ) ^ 3
        + (q τ) ^ 4 * kleinB_tail_eval (q τ) :=
  kleinBfunExt_q_of_mem_fd_eq_trunc (τ := τ) hτ

example {q : ℂ} (hq : ‖q‖ ≤ (1 / 100 : ℝ)) :
    (1228 : ℝ) ≤ ‖kleinB_trunc_poly q‖ :=
  norm_kleinB_trunc_poly_ge_1228 hq

example {q : ℂ} (hq : ‖q‖ ≤ (1 / 100 : ℝ)) (hq_lt : ‖q‖ < 1) (hq0 : q ≠ 0)
    (htail : ‖q ^ 4 * kleinB_tail_eval q‖ < (1200 : ℝ)) :
    kleinBfunExt q ≠ 0 :=
  kleinBfunExt_ne_zero_of_norm_le_one_div_hundred_of_tail_lt_1200 hq hq_lt hq0 htail

example (hDisc : KleinDiscriminantIdentity) (τ : ℍ) :
    kleinDenom τ = (1728 : ℂ) * Delta τ :=
  hDisc τ

example (hDisc : KleinDiscriminantIdentityCusp) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_cusp hDisc

example (hDisk : KleinDiscriminantIdentityOnUnitDisk) :
    KleinDiscriminantIdentityCusp :=
  kleinDiscriminantIdentityCusp_of_unitDisk hDisk

example (hDisk : KleinDiscriminantIdentityOnUnitDisk) :
    KleinDiscriminantIdentityOnPuncturedUnitDisk :=
  kleinDiscriminantIdentityOnPuncturedUnitDisk_of_unitDisk hDisk

example (hPunct : KleinDiscriminantIdentityOnPuncturedUnitDisk) :
    KleinDiscriminantIdentityCusp :=
  kleinDiscriminantIdentityCusp_of_puncturedUnitDisk hPunct

example (hCusp : KleinDiscriminantIdentityCusp) :
    KleinDiscriminantIdentityOnPuncturedUnitDisk :=
  kleinDiscriminantIdentityOnPuncturedUnitDisk_of_cusp hCusp

example :
    KleinDiscriminantIdentityCusp ↔ KleinDiscriminantIdentityOnPuncturedUnitDisk :=
  kleinDiscriminantIdentityCusp_iff_puncturedUnitDisk

example :
    KleinDiscriminantIdentity ↔ KleinDiscriminantIdentityCusp :=
  kleinDiscriminantIdentity_iff_cusp

example :
    KleinDiscriminantIdentity ↔ KleinDiscriminantIdentityOnPuncturedUnitDisk :=
  kleinDiscriminantIdentity_iff_puncturedUnitDisk

example :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔ KleinBfunExtDeltaIdentityOnUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_unitDisk

example (hPunct : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    KleinBfunExtDeltaIdentityCusp :=
  kleinBfunExtDeltaIdentityCusp_of_puncturedUnitDisk hPunct

example (hCusp : KleinBfunExtDeltaIdentityCusp) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_cusp hCusp

example :
    KleinBfunExtDeltaIdentityCusp ↔ KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityCusp_iff_puncturedUnitDisk

example (hPunct : KleinDiscriminantIdentityOnPuncturedUnitDisk) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_discriminant_puncturedUnitDisk hPunct

example (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    KleinDiscriminantIdentityOnPuncturedUnitDisk :=
  kleinDiscriminantIdentityOnPuncturedUnitDisk_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk hB

example :
    KleinDiscriminantIdentityOnPuncturedUnitDisk ↔
      KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinDiscriminantIdentityOnPuncturedUnitDisk_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk

example :
    KleinDiscriminantIdentityCusp ↔ KleinBfunExtDeltaIdentityCusp :=
  kleinDiscriminantIdentityCusp_iff_kleinBfunExtDeltaIdentityCusp

example (hDiscCusp : KleinDiscriminantIdentityCusp) :
    KleinBfunExtDeltaIdentityCusp :=
  kleinBfunExtDeltaIdentityCusp_of_discriminant_cusp hDiscCusp

example (hB : KleinBfunExtDeltaIdentityCusp) :
    KleinDiscriminantIdentityCusp :=
  kleinDiscriminantIdentityCusp_of_kleinBfunExtDeltaIdentityCusp hB

example :
    KleinDiscriminantIdentity ↔ KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk

example :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :=
  kleinDiscriminantIdentity_iff_etaIdentity

example :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :=
  kleinDiscriminantIdentity_iff_eisensteinEtaIdentity

example :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔
      (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_etaIdentity

example :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔
      (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eisensteinEtaIdentity

example :
    KleinDiscriminantIdentity ↔ KleinBfunExtDeltaIdentityCusp :=
  kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityCusp

example :
    KleinBfunExtDeltaIdentityCusp ↔
      (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :=
  kleinBfunExtDeltaIdentityCusp_iff_etaIdentity

example :
    KleinBfunExtDeltaIdentityCusp ↔
      (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :=
  kleinBfunExtDeltaIdentityCusp_iff_eisensteinEtaIdentity

example (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
    (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_eisensteinEtaIdentity hEta

example (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
    (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_eisensteinEtaIdentity hEta

example (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
    (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    KleinBfunExtDeltaIdentityCusp :=
  kleinBfunExtDeltaIdentityCusp_of_eisensteinEtaIdentity hEta

example (q : ℂ) (hq0 : q ≠ 0) :
    q⁻¹ * Delta_cusp q = deltaEulerProduct q :=
  inv_mul_Delta_cusp_eq_deltaEulerProduct q hq0

example : deltaEulerProduct 0 = 1 := deltaEulerProduct_zero

example {q : ℂ} (hq : ‖q‖ < 1) :
    deltaEulerProduct q ≠ 0 :=
  deltaEulerProduct_ne_zero_of_norm_lt_one hq

example {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    deltaEulerProduct q ≠ 0 :=
  deltaEulerProduct_ne_zero_of_norm_lt_one_of_ne_zero hq hq0

example (τ : ℍ) : deltaEulerProduct (q τ) ≠ 0 :=
  deltaEulerProduct_ne_zero_of_eq_q τ

example :
    kleinBfunExt 0 = (1728 : ℂ) * deltaEulerProduct 0 :=
  kleinBfunExt_eq_1728_mul_deltaEulerProduct_zero

example :
    kleinBfunExt 0 - (1728 : ℂ) * deltaEulerProduct 0 = 0 :=
  kleinBfunExt_sub_1728_mul_deltaEulerProduct_zero

example : kleinEulerRatio 0 = 1 := kleinEulerRatio_zero

example :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔
      (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q) :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eulerProduct

example :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔
      (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1) :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_kleinEulerRatio_eq_one

example :
    KleinBfunExtDeltaIdentityCusp ↔
      (∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) :=
  kleinBfunExtDeltaIdentityCusp_iff_eulerProduct

example :
    KleinBfunExtDeltaIdentityCusp ↔
      (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :=
  kleinBfunExtDeltaIdentityCusp_iff_kleinEulerRatio_eq_one

example {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    kleinEulerRatio q = 1 ↔ kleinDfun q = (1728 : ℂ) * Delta_cusp q :=
  kleinEulerRatio_eq_one_iff_discriminant_punctured hq hq0

example (τ : ℍ) :
    kleinEulerRatio (q τ) = 1 ↔ kleinDenom τ = (1728 : ℂ) * Delta τ :=
  kleinEulerRatio_eq_one_iff_discriminant_at_cusp τ

example (τ : ℍ) :
    kleinEulerRatio (q τ) = 1 ↔
      (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat) :=
  kleinEulerRatio_eq_one_iff_eisensteinEta_at_cusp τ

example :
    (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) ↔
      (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
        (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :=
  kleinEulerRatioCusp_iff_eisensteinEtaIdentity_pointwise

example (τ : ℍ) :
    kleinEulerRatio (q τ) = kleinDenom τ / ((1728 : ℂ) * Delta τ) :=
  kleinEulerRatio_at_cusp_eq_div τ

example :
    (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) ↔
      (∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :=
  kleinEulerRatioCusp_eq_one_iff_kleinDenom_div_Delta_eq_1728

example (hDiv : ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :
    ∀ τ : ℍ, kleinEulerRatio (q τ) = 1 :=
  kleinEulerRatioCusp_of_kleinDenom_div_Delta_eq_1728 hDiv

example (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) :=
  kleinDenom_div_Delta_eq_1728_of_kleinEulerRatioCusp hRatio

example (hDiv : ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_kleinDenom_div_Delta_eq_1728 hDiv

example (hDiv : ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_kleinDenom_div_Delta_eq_1728 hDiv

example (hDisc : KleinDiscriminantIdentity) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) :=
  kleinDenom_div_Delta_eq_1728_of_kleinDiscriminantIdentity hDisc

example :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :=
  kleinDiscriminantIdentity_iff_kleinDenom_div_Delta_eq_1728

example (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ)
    (τ0 : ℍ) (hAt : f τ0 = (1728 : ℂ)) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) :=
  kleinDenom_div_Delta_eq_1728_of_ratio_modularForm_weight_zero f hRatio τ0 hAt

example (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ)
    (τ0 : ℍ) (hAt : f τ0 = (1728 : ℂ)) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_ratio_modularForm_weight_zero f hRatio τ0 hAt

example (f : ModularForm Γ(1) 0)
    (hRatio : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ)
    (τ0 : ℍ) (hAt : f τ0 = (1728 : ℂ)) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_ratio_modularForm_weight_zero f hRatio τ0 hAt

example (τ0 : ℍ) :
    KleinDiscriminantIdentity ↔
      ∃ f : ModularForm Γ(1) 0,
        (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) :=
  kleinDiscriminantIdentity_iff_exists_ratio_modularForm_weight_zero τ0

example (τ0 : ℍ) :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      ∃ f : ModularForm Γ(1) 0,
        (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) :=
  eisensteinEtaIdentity_iff_exists_ratio_modularForm_weight_zero τ0

example (τ0 : ℍ) :
    KleinDiscriminantIdentity ↔ Nonempty (KleinRatioWitness τ0) :=
  kleinDiscriminantIdentity_iff_nonempty_witness τ0

example (τ0 : ℍ) (hDisc : KleinDiscriminantIdentity) :
    Nonempty (KleinRatioWitness τ0) :=
  nonempty_witness_of_kleinDiscriminantIdentity τ0 hDisc

example (τ0 : ℍ) (hW : Nonempty (KleinRatioWitness τ0)) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_nonempty_witness τ0 hW

example (τ0 : ℍ) :
    (∃ f : ModularForm Γ(1) 0,
      (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ)) ↔
      Nonempty (KleinRatioWitness τ0) :=
  exists_ratio_modularForm_weight_zero_iff_nonempty_witness τ0

example (τ0 : ℍ)
    (w : KleinRatioWitness τ0) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_witness w

example (τ0 : ℍ)
    (w : KleinRatioWitness τ0) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_witness w

example (τ0 : ℍ) (hDisc : KleinDiscriminantIdentity) :
    KleinRatioWitness τ0 :=
  witnessOfKleinDiscriminantIdentity τ0 hDisc

example (τ0 : ℍ) :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      Nonempty (KleinRatioWitness τ0) :=
  eisensteinEtaIdentity_iff_nonempty_witness τ0

example (τ0 : ℍ)
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    Nonempty (KleinRatioWitness τ0) :=
  nonempty_witness_of_eisensteinEtaIdentity τ0 hEta

example (τ0 : ℍ) (hW : Nonempty (KleinRatioWitness τ0)) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) :=
  eisensteinEtaIdentity_of_nonempty_witness τ0 hW

example (τ0 : ℍ) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔ Nonempty (KleinRatioWitness τ0) :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_nonempty_witness τ0

example (τ0 : ℍ) (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    Nonempty (KleinRatioWitness τ0) :=
  nonempty_witness_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk τ0 hB

example (τ0 : ℍ) (hW : Nonempty (KleinRatioWitness τ0)) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_nonempty_witness τ0 hW

example (τ0 : ℍ) :
    KleinBfunExtDeltaIdentityCusp ↔ Nonempty (KleinRatioWitness τ0) :=
  kleinBfunExtDeltaIdentityCusp_iff_nonempty_witness τ0

example (τ0 : ℍ) (hB : KleinBfunExtDeltaIdentityCusp) :
    Nonempty (KleinRatioWitness τ0) :=
  nonempty_witness_of_kleinBfunExtDeltaIdentityCusp τ0 hB

example (τ0 : ℍ) (hW : Nonempty (KleinRatioWitness τ0)) :
    KleinBfunExtDeltaIdentityCusp :=
  kleinBfunExtDeltaIdentityCusp_of_nonempty_witness τ0 hW

example (τ0 : ℍ) (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    ∃ f : ModularForm Γ(1) 0,
      (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) :=
  exists_ratio_modularForm_weight_zero_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk τ0 hB

example (τ0 : ℍ) (hB : KleinBfunExtDeltaIdentityCusp) :
    ∃ f : ModularForm Γ(1) 0,
      (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) :=
  exists_ratio_modularForm_weight_zero_of_kleinBfunExtDeltaIdentityCusp τ0 hB

example :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      (∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) :=
  eisensteinEtaIdentity_iff_eulerProductCusp

example :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
        kleinBfunExt q = (1728 : ℂ) * deltaEulerProduct q) :=
  eisensteinEtaIdentity_iff_eulerProductPunctured

example (hEulerCusp : ∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) :=
  eisensteinEtaIdentity_of_eulerProductCusp hEulerCusp

example (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
    (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ) :=
  eulerProductCusp_of_eisensteinEtaIdentity hEta

example :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      (∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :=
  eisensteinEtaIdentity_iff_kleinEulerRatioCusp

example :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      (∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1) :=
  eisensteinEtaIdentity_iff_kleinEulerRatioPunctured

example (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) :=
  eisensteinEtaIdentity_of_kleinEulerRatioCusp hRatio

example (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
    (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ τ : ℍ, kleinEulerRatio (q τ) = 1 :=
  kleinEulerRatioCusp_of_eisensteinEtaIdentity hEta

example (hRatio : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) :=
  eisensteinEtaIdentity_of_kleinEulerRatioPunctured hRatio

example (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
    (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinEulerRatio q = 1 :=
  kleinEulerRatioPunctured_of_eisensteinEtaIdentity hEta

example (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_kleinEulerRatioCusp hRatio

example (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_kleinEulerRatioCusp hRatio

example (hRatio : ∀ τ : ℍ, kleinEulerRatio (q τ) = 1) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_kleinEulerRatioCusp hRatio τ

example (τ : ℍ) : Delta τ = q τ * deltaEulerProduct (q τ) :=
  Delta_eq_q_mul_deltaEulerProduct τ

example (τ : ℍ) : deltaEulerProduct (q τ) = (q τ)⁻¹ * Delta τ :=
  deltaEulerProduct_eq_inv_mul_Delta_of_eq_q τ

example (τ : ℍ) : (q τ) * deltaEulerProduct (q τ) = Delta τ :=
  deltaEulerProduct_mul_q_eq_Delta τ

example :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (q τ) * deltaEulerProduct (q τ)) :=
  kleinDiscriminantIdentity_iff_q_mul_eulerProduct

example :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) :=
  kleinDiscriminantIdentity_iff_eulerProductCusp

example (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk hB

example (hB : KleinBfunExtDeltaIdentityCusp) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_kleinBfunExtDeltaIdentityCusp hB

example (hDisc : KleinDiscriminantIdentity) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_discriminant_identity hDisc

example (hDisc : KleinDiscriminantIdentity) :
    KleinBfunExtDeltaIdentityCusp :=
  kleinBfunExtDeltaIdentityCusp_of_discriminant_identity hDisc

example (hDisk : KleinDiscriminantIdentityOnUnitDisk) :
    KleinBfunExtDeltaIdentityOnUnitDisk :=
  kleinBfunExtDeltaIdentityOnUnitDisk_of_discriminant_unitDisk hDisk

example (hB : KleinBfunExtDeltaIdentityOnUnitDisk) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityOnUnitDisk hB τ

example (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk hB τ

example (hB : KleinBfunExtDeltaIdentityCusp) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityCusp hB τ

example (hEulerCusp : ∀ τ : ℍ, kleinBfunExt (q τ) = (1728 : ℂ) * deltaEulerProduct (q τ)) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_eulerProductCusp hEulerCusp τ

example (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
    (1728 : ℂ) * (eta τ) ^ (24 : Nat)) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_eisensteinEtaIdentity hEta τ

example (hDisc : KleinDiscriminantIdentity) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_discriminant_identity hDisc τ

example (hPunct : KleinDiscriminantIdentityOnPuncturedUnitDisk) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_discriminant_punctured_unitDisk hPunct τ

example (hB : KleinBfunExtDeltaIdentityCusp) (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_on_fd_of_kleinBfunExtDeltaIdentityCusp hB τ hτ

example (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ‖q ^ 4 * kleinB_tail_eval q‖
      ≤ ∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ‖q‖ ^ (n + 4) :=
  norm_q_pow_four_mul_kleinB_tail_eval_le_tsum_coeff (q := q) hq hq0

example
    (hCoeffFd : ∀ τ : ℍ, τ ∈ ModularGroup.fd →
      (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ‖q τ‖ ^ (n + 4)) < (1200 : ℝ))
    (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_fd_coeff_majorant_lt_1200 hCoeffFd τ

example
    (hSummable100 :
      Summable (fun n : ℕ => ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))))
    (hBound100 :
      (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))) < (1200 : ℝ))
    (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_coeff_majorant_one_div_hundred_lt_1200 hSummable100 hBound100 τ

example :
    Summable (fun n : ℕ => ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))) :=
  summable_coeff_majorant_one_div_hundred

example
    (hBound100 :
      (∑' n : ℕ, ‖kleinBps.coeff (n + 4)‖ * ((1 / 100 : ℝ) ^ (n + 4))) < (1200 : ℝ))
    (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_coeff_majorant_one_div_hundred_lt_1200' hBound100 τ

example (G : Type*) [Group G] :
    (kleinJ₀_levelOneHauptmodulData (G := G)).genusZero :=
  kleinJ₀_levelOneHauptmodulData_genusZero (G := G)

example (G : Type*) [Group G] :
    (kleinJ₀_levelOneHauptmodulData (G := G)).qExp = J_q :=
  kleinJ₀_levelOneHauptmodulData_qExp (G := G)

example (τ0 : ℍ) (hW : Nonempty (KleinRatioWitness τ0)) (τ : ℍ) :
    kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_nonempty_witness τ0 hW τ

example (τ0 : ℍ) (hW : Nonempty (KleinRatioWitness τ0)) :
    IsHauptmodulWithDenom (⊤ : Subgroup SL2Z) kleinJ₀ kleinDenom :=
  kleinJ₀_isHauptmodulWithDenom_of_nonempty_witness τ0 hW

example (g : SL(2, ℤ)) (τ : ℍ) :
    DeltaLevelOne (g • τ) = (UpperHalfPlane.denom g τ) ^ (12 : Nat) * DeltaLevelOne τ :=
  hDeltaSmul g τ

example (τ : ℍ) :
    kleinDenom τ / DeltaLevelOne τ = (1728 : ℂ) :=
  hDiv_of_Delta_smul τ

end HeytingLean.Moonshine.Modular
