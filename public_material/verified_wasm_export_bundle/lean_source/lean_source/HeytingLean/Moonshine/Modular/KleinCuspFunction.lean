import HeytingLean.Moonshine.Modular.JInvariant
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

open scoped CongruenceSubgroup
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

/-- The cusp function `F₄` such that `E4 τ = F₄(𝕢 1 τ)` (level 1). -/
noncomputable def E4_cusp : ℂ → ℂ :=
  SlashInvariantFormClass.cuspFunction 1 E4

/-- The cusp function `F₆` such that `E6 τ = F₆(𝕢 1 τ)` (level 1). -/
noncomputable def E6_cusp : ℂ → ℂ :=
  SlashInvariantFormClass.cuspFunction 1 E6

lemma E4_eq_E4_cusp (τ : ℍ) : E4_cusp (𝕢 1 τ) = E4 τ := by
  simpa [E4_cusp] using (SlashInvariantFormClass.eq_cuspFunction (n := 1) (f := E4) τ)

lemma E6_eq_E6_cusp (τ : ℍ) : E6_cusp (𝕢 1 τ) = E6 τ := by
  simpa [E6_cusp] using (SlashInvariantFormClass.eq_cuspFunction (n := 1) (f := E6) τ)

lemma differentiableAt_E4_cusp {q : ℂ} (hq : ‖q‖ < 1) : DifferentiableAt ℂ E4_cusp q := by
  simpa [E4_cusp] using (ModularFormClass.differentiableAt_cuspFunction (n := 1) (f := E4) hq)

lemma differentiableAt_E6_cusp {q : ℂ} (hq : ‖q‖ < 1) : DifferentiableAt ℂ E6_cusp q := by
  simpa [E6_cusp] using (ModularFormClass.differentiableAt_cuspFunction (n := 1) (f := E6) hq)

lemma hasSum_qExpansion₁_E4_cusp {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion₁ E4).coeff m • q ^ m) (E4_cusp q) := by
  simpa [E4_cusp] using (hasSum_qExpansion₁_cusp (f := E4) hq)

lemma hasSum_qExpansion₁_E6_cusp {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion₁ E6).coeff m • q ^ m) (E6_cusp q) := by
  simpa [E6_cusp] using (hasSum_qExpansion₁_cusp (f := E6) hq)

lemma E4_cusp_eq_tsum_qExpansion₁ {q : ℂ} (hq : ‖q‖ < 1) :
    E4_cusp q = ∑' m : ℕ, (qExpansion₁ E4).coeff m * q ^ m := by
  -- Convert `•` to `*` and take `tsum`.
  simpa [smul_eq_mul] using (hasSum_qExpansion₁_E4_cusp (q := q) hq).tsum_eq.symm

lemma E6_cusp_eq_tsum_qExpansion₁ {q : ℂ} (hq : ‖q‖ < 1) :
    E6_cusp q = ∑' m : ℕ, (qExpansion₁ E6).coeff m * q ^ m := by
  simpa [smul_eq_mul] using (hasSum_qExpansion₁_E6_cusp (q := q) hq).tsum_eq.symm

/--
The Klein `j`-invariant expressed as a rational function of the cusp functions `E4_cusp`, `E6_cusp`.

This is the main "q-parametrization" bridge: once we control Taylor expansions of `E4_cusp` and
`E6_cusp` at `0`, we can derive the Laurent expansion of `kleinJ` at infinity.
-/
noncomputable def kleinJ_cusp (q : ℂ) : ℂ :=
  (1728 : ℂ) * (E4_cusp q) ^ 3 / ((E4_cusp q) ^ 3 - (E6_cusp q) ^ 2)

noncomputable def kleinJ₀_cusp (q : ℂ) : ℂ :=
  kleinJ_cusp q - 744

lemma kleinJ_cusp_eq_rational_tsum_qExpansion₁ {q : ℂ} (hq : ‖q‖ < 1) :
    kleinJ_cusp q =
      (1728 : ℂ) *
        (∑' m : ℕ, (qExpansion₁ E4).coeff m * q ^ m) ^ (3 : ℕ) /
          ((∑' m : ℕ, (qExpansion₁ E4).coeff m * q ^ m) ^ (3 : ℕ) -
            (∑' m : ℕ, (qExpansion₁ E6).coeff m * q ^ m) ^ (2 : ℕ)) := by
  simp [kleinJ_cusp, E4_cusp_eq_tsum_qExpansion₁ (q := q) hq, E6_cusp_eq_tsum_qExpansion₁ (q := q) hq]

lemma kleinJ₀_cusp_eq_rational_tsum_qExpansion₁ {q : ℂ} (hq : ‖q‖ < 1) :
    kleinJ₀_cusp q =
      (1728 : ℂ) *
        (∑' m : ℕ, (qExpansion₁ E4).coeff m * q ^ m) ^ (3 : ℕ) /
          ((∑' m : ℕ, (qExpansion₁ E4).coeff m * q ^ m) ^ (3 : ℕ) -
            (∑' m : ℕ, (qExpansion₁ E6).coeff m * q ^ m) ^ (2 : ℕ)) - 744 := by
  simp [kleinJ₀_cusp, kleinJ_cusp_eq_rational_tsum_qExpansion₁ (q := q) hq]

lemma kleinJ_eq_kleinJ_cusp (τ : ℍ) : kleinJ τ = kleinJ_cusp (𝕢 1 τ) := by
  simp [kleinJ, kleinJ_cusp, E4_eq_E4_cusp, E6_eq_E6_cusp]

lemma kleinJ₀_eq_kleinJ₀_cusp (τ : ℍ) : kleinJ₀ τ = kleinJ₀_cusp (𝕢 1 τ) := by
  simp [kleinJ₀, kleinJ₀_cusp, kleinJ_eq_kleinJ_cusp]

end HeytingLean.Moonshine.Modular
