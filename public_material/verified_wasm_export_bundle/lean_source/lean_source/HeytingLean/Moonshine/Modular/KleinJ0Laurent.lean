import HeytingLean.Moonshine.Modular.EisensteinQExpansion
import HeytingLean.Moonshine.Modular.JSeries

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.HahnSeries.PowerSeries

import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open scoped BigOperators

/-!
## `J(q)` coefficients from `E4/E6` q-expansions (kernel-pure)

Using:
- `qExpansion₁_E4_eq_expected : qExpansion₁ E4 = E4_q_expected`
- `qExpansion₁_E6_eq_expected : qExpansion₁ E6 = E6_q_expected`

we compute the Laurent coefficients of the formal series
`j(q) = 1728 * E4(q)^3 / (E4(q)^3 - E6(q)^2)` and hence `J(q) = j(q) - 744`,
matching the hard-coded reference series `JSeries.J_q` at exponents `-1,0,1,2`.

This is the formal-algebraic side of the Klein cusp bridge in `KleinCuspFunction.lean`.
-/

abbrev kleinDSeries (E4ps E6ps : PowerSeries ℂ) : PowerSeries ℂ :=
  E4ps ^ (3 : ℕ) - E6ps ^ (2 : ℕ)

abbrev kleinBSeries (E4ps E6ps : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (kleinDSeries E4ps E6ps)

abbrev kleinASeries (E4ps E6ps : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C (1728 : ℂ) * (E4ps ^ (3 : ℕ)) * (kleinBSeries E4ps E6ps)⁻¹

/-- Formal Laurent/q-series for `j(q)` built from `E4/E6` q-expansions. -/
noncomputable def kleinJ_qLaurent (E4ps E6ps : PowerSeries ℂ) : HahnSeries ℤ ℂ :=
  HahnSeries.single (-1 : ℤ) (1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (kleinASeries E4ps E6ps)

/-- Formal Laurent/q-series for `J(q) = j(q) - 744`. -/
noncomputable def kleinJ₀_qLaurent (E4ps E6ps : PowerSeries ℂ) : HahnSeries ℤ ℂ :=
  kleinJ_qLaurent E4ps E6ps - HahnSeries.C (744 : ℂ)

/-!
### Low-degree coefficient helpers for power series multiplication

We rewrite `coeff n (φ * ψ)` into an explicit finite sum using
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` and then expand that sum for `n ≤ 4`.
-/

private lemma coeff_mul_two (φ ψ : PowerSeries ℂ) :
    PowerSeries.coeff 2 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 2 ψ
        + PowerSeries.coeff 1 φ * PowerSeries.coeff 1 ψ
        + PowerSeries.coeff 2 φ * PowerSeries.coeff 0 ψ := by
  classical
  -- `coeff_mul` is an antidiagonal sum; convert to a range sum and expand.
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

private lemma coeff_mul_one (φ ψ : PowerSeries ℂ) :
    PowerSeries.coeff 1 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 1 ψ
        + PowerSeries.coeff 1 φ * PowerSeries.coeff 0 ψ := by
  classical
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

private lemma coeff_mul_three (φ ψ : PowerSeries ℂ) :
    PowerSeries.coeff 3 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 3 ψ
        + PowerSeries.coeff 1 φ * PowerSeries.coeff 2 ψ
        + PowerSeries.coeff 2 φ * PowerSeries.coeff 1 ψ
        + PowerSeries.coeff 3 φ * PowerSeries.coeff 0 ψ := by
  classical
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

private lemma coeff_mul_four (φ ψ : PowerSeries ℂ) :
    PowerSeries.coeff 4 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 4 ψ
        + PowerSeries.coeff 1 φ * PowerSeries.coeff 3 ψ
        + PowerSeries.coeff 2 φ * PowerSeries.coeff 2 ψ
        + PowerSeries.coeff 3 φ * PowerSeries.coeff 1 ψ
        + PowerSeries.coeff 4 φ * PowerSeries.coeff 0 ψ := by
  classical
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

/-!
### Coefficients of the expected `E4/E6` power series and their composites
-/

private lemma constantCoeff_E4_expected : PowerSeries.constantCoeff E4_q_expected = (1 : ℂ) := by
  -- Avoid `simp` turning the coefficient lemma into `True`.
  have h : PowerSeries.coeff 0 E4_q_expected = (1 : ℂ) :=
    E4_q_expected_coeff_zero
  calc
    PowerSeries.constantCoeff E4_q_expected = PowerSeries.coeff 0 E4_q_expected := by
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    _ = (1 : ℂ) := h

private lemma constantCoeff_E6_expected : PowerSeries.constantCoeff E6_q_expected = (1 : ℂ) := by
  have h : PowerSeries.coeff 0 E6_q_expected = (1 : ℂ) :=
    E6_q_expected_coeff_zero
  calc
    PowerSeries.constantCoeff E6_q_expected = PowerSeries.coeff 0 E6_q_expected := by
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    _ = (1 : ℂ) := h

private lemma coeff_E4_sq_expected_0 :
    PowerSeries.coeff 0 (E4_q_expected ^ (2 : ℕ)) = (1 : ℂ) := by
  -- Coefficient `0` in a product only sees the constant terms.
  simp [pow_two, PowerSeries.coeff_mul, E4_q_expected_coeff_zero]

private lemma coeff_E4_sq_expected_1 :
    PowerSeries.coeff 1 (E4_q_expected ^ (2 : ℕ)) = (480 : ℂ) := by
  -- Use the dedicated `coeff_one_mul` lemma.
  have h :=
    (PowerSeries.coeff_one_mul (φ := E4_q_expected) (ψ := E4_q_expected) (R := ℂ))
  have h' :
      PowerSeries.coeff 1 (E4_q_expected * E4_q_expected) = (240 : ℂ) + 240 := by
    simpa [constantCoeff_E4_expected, E4_q_expected_coeff_one, two_mul, add_assoc] using h
  have h'' : PowerSeries.coeff 1 (E4_q_expected * E4_q_expected) = (480 : ℂ) := by
    -- Evaluate `240 + 240`.
    simpa using (h'.trans (by norm_num : ((240 : ℂ) + 240) = 480))
  simpa [pow_two] using h''

private lemma coeff_E4_sq_expected_2 :
    PowerSeries.coeff 2 (E4_q_expected ^ (2 : ℕ)) = (61920 : ℂ) := by
  simp [pow_two, coeff_mul_two, E4_q_expected_coeff_zero, E4_q_expected_coeff_one,
    E4_q_expected_coeff_two]
  norm_num

private lemma coeff_E4_sq_expected_3 :
    PowerSeries.coeff 3 (E4_q_expected ^ (2 : ℕ)) = (1050240 : ℂ) := by
  simp [pow_two, coeff_mul_three, E4_q_expected_coeff_zero, E4_q_expected_coeff_one,
    E4_q_expected_coeff_two, E4_q_expected_coeff_three]
  norm_num

private lemma coeff_E4_sq_expected_4 :
    PowerSeries.coeff 4 (E4_q_expected ^ (2 : ℕ)) = (7926240 : ℂ) := by
  simp [pow_two, coeff_mul_four, E4_q_expected_coeff_zero, E4_q_expected_coeff_one,
    E4_q_expected_coeff_two, E4_q_expected_coeff_three, E4_q_expected_coeff_four]
  norm_num

private lemma coeff_E4_cube_expected_0 :
    PowerSeries.coeff 0 (E4_q_expected ^ (3 : ℕ)) = (1 : ℂ) := by
  -- `coeff 0` is `constantCoeff`.
  simp [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_E4_expected]

private lemma coeff_E4_cube_expected_1 :
    PowerSeries.coeff 1 (E4_q_expected ^ (3 : ℕ)) = (720 : ℂ) := by
  -- Reuse the lemma already proved in the expected-expansion file.
  simpa using (coeff_one_E4_q_expected_pow_three : _)

private lemma coeff_E4_cube_expected_2 :
    PowerSeries.coeff 2 (E4_q_expected ^ (3 : ℕ)) = (179280 : ℂ) := by
  -- `E4^3 = (E4^2) * E4`.
  have h : E4_q_expected ^ (3 : ℕ) = (E4_q_expected ^ (2 : ℕ)) * E4_q_expected := by
    simpa using (pow_succ E4_q_expected 2)
  -- Expand `coeff 2` of the product.
  simp [h, coeff_mul_two, coeff_E4_sq_expected_0, coeff_E4_sq_expected_1, coeff_E4_sq_expected_2,
    E4_q_expected_coeff_zero, E4_q_expected_coeff_one, E4_q_expected_coeff_two]
  norm_num

private lemma coeff_E4_cube_expected_3 :
    PowerSeries.coeff 3 (E4_q_expected ^ (3 : ℕ)) = (16954560 : ℂ) := by
  have h : E4_q_expected ^ (3 : ℕ) = (E4_q_expected ^ (2 : ℕ)) * E4_q_expected := by
    simpa using (pow_succ E4_q_expected 2)
  simp [h, coeff_mul_three, coeff_E4_sq_expected_0, coeff_E4_sq_expected_1, coeff_E4_sq_expected_2,
    coeff_E4_sq_expected_3, E4_q_expected_coeff_zero, E4_q_expected_coeff_one,
    E4_q_expected_coeff_two, E4_q_expected_coeff_three]
  norm_num

private lemma coeff_E4_cube_expected_4 :
    PowerSeries.coeff 4 (E4_q_expected ^ (3 : ℕ)) = (396974160 : ℂ) := by
  have h : E4_q_expected ^ (3 : ℕ) = (E4_q_expected ^ (2 : ℕ)) * E4_q_expected := by
    simpa using (pow_succ E4_q_expected 2)
  simp [h, coeff_mul_four, coeff_E4_sq_expected_0, coeff_E4_sq_expected_1, coeff_E4_sq_expected_2,
    coeff_E4_sq_expected_3, coeff_E4_sq_expected_4, E4_q_expected_coeff_zero, E4_q_expected_coeff_one,
    E4_q_expected_coeff_two, E4_q_expected_coeff_three, E4_q_expected_coeff_four]
  norm_num

private lemma coeff_E6_sq_expected_0 :
    PowerSeries.coeff 0 (E6_q_expected ^ (2 : ℕ)) = (1 : ℂ) := by
  simp [pow_two, PowerSeries.coeff_mul, E6_q_expected_coeff_zero]

private lemma coeff_E6_sq_expected_1 :
    PowerSeries.coeff 1 (E6_q_expected ^ (2 : ℕ)) = (-1008 : ℂ) := by
  simpa using (coeff_one_E6_q_expected_pow_two : _)

private lemma coeff_E6_sq_expected_2 :
    PowerSeries.coeff 2 (E6_q_expected ^ (2 : ℕ)) = (220752 : ℂ) := by
  simp [pow_two, coeff_mul_two, E6_q_expected_coeff_zero, E6_q_expected_coeff_one, E6_q_expected_coeff_two]
  norm_num

private lemma coeff_E6_sq_expected_3 :
    PowerSeries.coeff 3 (E6_q_expected ^ (2 : ℕ)) = (16519104 : ℂ) := by
  simp [pow_two, coeff_mul_three, E6_q_expected_coeff_zero, E6_q_expected_coeff_one,
    E6_q_expected_coeff_two, E6_q_expected_coeff_three]
  norm_num

private lemma coeff_E6_sq_expected_4 :
    PowerSeries.coeff 4 (E6_q_expected ^ (2 : ℕ)) = (399517776 : ℂ) := by
  simp [pow_two, coeff_mul_four, E6_q_expected_coeff_zero, E6_q_expected_coeff_one,
    E6_q_expected_coeff_two, E6_q_expected_coeff_three, E6_q_expected_coeff_four]
  norm_num

private lemma coeff_D_expected_0 :
    PowerSeries.coeff 0 (kleinDSeries E4_q_expected E6_q_expected) = (0 : ℂ) := by
  -- Use the fact that both `E4_q_expected` and `E6_q_expected` have constant coefficient `1`.
  simp [kleinDSeries, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_E4_expected,
    constantCoeff_E6_expected]

private lemma coeff_D_expected_1 :
    PowerSeries.coeff 1 (kleinDSeries E4_q_expected E6_q_expected) = (1728 : ℂ) := by
  -- This is already in `EisensteinExpectedQExpansion.lean`.
  simpa [kleinDSeries] using (coeff_one_E4_cubed_sub_E6_sq_expected : _)

private lemma coeff_D_expected_2 :
    PowerSeries.coeff 2 (kleinDSeries E4_q_expected E6_q_expected) = (-41472 : ℂ) := by
  simp [kleinDSeries, coeff_E4_cube_expected_2, coeff_E6_sq_expected_2]
  norm_num

private lemma coeff_D_expected_3 :
    PowerSeries.coeff 3 (kleinDSeries E4_q_expected E6_q_expected) = (435456 : ℂ) := by
  simp [kleinDSeries, coeff_E4_cube_expected_3, coeff_E6_sq_expected_3]
  norm_num

private lemma coeff_D_expected_4 :
    PowerSeries.coeff 4 (kleinDSeries E4_q_expected E6_q_expected) = (-2543616 : ℂ) := by
  simp [kleinDSeries, coeff_E4_cube_expected_4, coeff_E6_sq_expected_4]
  norm_num

private lemma coeff_B_expected_0 :
    PowerSeries.coeff 0 (kleinBSeries E4_q_expected E6_q_expected) = (1728 : ℂ) := by
  simpa [kleinBSeries] using coeff_D_expected_1

private lemma coeff_B_expected_1 :
    PowerSeries.coeff 1 (kleinBSeries E4_q_expected E6_q_expected) = (-41472 : ℂ) := by
  simpa [kleinBSeries] using coeff_D_expected_2

private lemma coeff_B_expected_2 :
    PowerSeries.coeff 2 (kleinBSeries E4_q_expected E6_q_expected) = (435456 : ℂ) := by
  simpa [kleinBSeries] using coeff_D_expected_3

private lemma coeff_B_expected_3 :
    PowerSeries.coeff 3 (kleinBSeries E4_q_expected E6_q_expected) = (-2543616 : ℂ) := by
  simpa [kleinBSeries] using coeff_D_expected_4

/-- Coefficient `q^1` of `E4^3 - E6^2` on the expected Eisenstein expansions. -/
theorem coeff_kleinDSeries_expected_1 :
    PowerSeries.coeff 1 (kleinDSeries E4_q_expected E6_q_expected) = (1728 : ℂ) :=
  coeff_D_expected_1

/-- Coefficient `q^2` of `E4^3 - E6^2` on the expected Eisenstein expansions. -/
theorem coeff_kleinDSeries_expected_2 :
    PowerSeries.coeff 2 (kleinDSeries E4_q_expected E6_q_expected) = (-41472 : ℂ) :=
  coeff_D_expected_2

/-- Coefficient `q^3` of `E4^3 - E6^2` on the expected Eisenstein expansions. -/
theorem coeff_kleinDSeries_expected_3 :
    PowerSeries.coeff 3 (kleinDSeries E4_q_expected E6_q_expected) = (435456 : ℂ) :=
  coeff_D_expected_3

/-- Coefficient `q^4` of `E4^3 - E6^2` on the expected Eisenstein expansions. -/
theorem coeff_kleinDSeries_expected_4 :
    PowerSeries.coeff 4 (kleinDSeries E4_q_expected E6_q_expected) = (-2543616 : ℂ) :=
  coeff_D_expected_4

/-- Constant coefficient of the shifted denominator series `kleinBSeries`. -/
theorem coeff_kleinBSeries_expected_0 :
    PowerSeries.coeff 0 (kleinBSeries E4_q_expected E6_q_expected) = (1728 : ℂ) :=
  coeff_B_expected_0

/-- Coefficient `q^1` of the shifted denominator series `kleinBSeries`. -/
theorem coeff_kleinBSeries_expected_1 :
    PowerSeries.coeff 1 (kleinBSeries E4_q_expected E6_q_expected) = (-41472 : ℂ) :=
  coeff_B_expected_1

/-- Coefficient `q^2` of the shifted denominator series `kleinBSeries`. -/
theorem coeff_kleinBSeries_expected_2 :
    PowerSeries.coeff 2 (kleinBSeries E4_q_expected E6_q_expected) = (435456 : ℂ) :=
  coeff_B_expected_2

/-- Coefficient `q^3` of the shifted denominator series `kleinBSeries`. -/
theorem coeff_kleinBSeries_expected_3 :
    PowerSeries.coeff 3 (kleinBSeries E4_q_expected E6_q_expected) = (-2543616 : ℂ) :=
  coeff_B_expected_3

private lemma constCoeff_B_expected_ne_zero :
    PowerSeries.constantCoeff (kleinBSeries E4_q_expected E6_q_expected) ≠ (0 : ℂ) := by
  have hcc : PowerSeries.constantCoeff (kleinBSeries E4_q_expected E6_q_expected) = (1728 : ℂ) := by
    calc
      PowerSeries.constantCoeff (kleinBSeries E4_q_expected E6_q_expected) =
          PowerSeries.coeff 0 (kleinBSeries E4_q_expected E6_q_expected) := by
            simp
      _ = (1728 : ℂ) := coeff_B_expected_0
  -- Reduce to a numeric nonzero claim.
  rw [hcc]
  norm_num

/-!
### Coefficients of `B⁻¹` and `A` (expected)
-/

private abbrev Bexp : PowerSeries ℂ := kleinBSeries E4_q_expected E6_q_expected
private abbrev Binvexp : PowerSeries ℂ := (Bexp)⁻¹

private lemma constantCoeff_Bexp : PowerSeries.constantCoeff Bexp = (1728 : ℂ) := by
  -- `Bexp` is just `BSeries ...`.
  have h0 : PowerSeries.coeff 0 Bexp = (1728 : ℂ) := coeff_B_expected_0
  calc
    PowerSeries.constantCoeff Bexp = PowerSeries.coeff 0 Bexp := by
      simp
    _ = (1728 : ℂ) := h0

private lemma coeff_Binv_expected_0 : PowerSeries.coeff 0 Binvexp = ((1 : ℂ) / 1728) := by
  -- `coeff 0` is `constantCoeff`.
  have hcc : PowerSeries.constantCoeff Binvexp = (PowerSeries.constantCoeff Bexp)⁻¹ := by
    simp [Binvexp]
  -- Convert to a coefficient statement and evaluate.
  have : PowerSeries.coeff 0 Binvexp = (1728 : ℂ)⁻¹ := by
    calc
      PowerSeries.coeff 0 Binvexp = PowerSeries.constantCoeff Binvexp := by
        simp
      _ = (PowerSeries.constantCoeff Bexp)⁻¹ := hcc
      _ = (1728 : ℂ)⁻¹ := by
            -- Avoid `simp` unfolding `Bexp`.
            simpa using congrArg (fun z : ℂ => z⁻¹) constantCoeff_Bexp
  simpa [one_div] using this

private lemma coeff_Binv_expected_1 : PowerSeries.coeff 1 Binvexp = ((1 : ℂ) / 72) := by
  have hmul : Bexp * Binvexp = (1 : PowerSeries ℂ) := by
    simpa [Bexp, Binvexp] using
      (PowerSeries.mul_inv_cancel (φ := Bexp) (h := constCoeff_B_expected_ne_zero))
  have hcoeff1 : PowerSeries.coeff 1 (Bexp * Binvexp) = 0 := by
    -- Take coefficients in the identity `B * B⁻¹ = 1`.
    have := congrArg (fun s : PowerSeries ℂ => PowerSeries.coeff 1 s) hmul
    simpa [PowerSeries.coeff_one] using this
  have hformula :=
    (PowerSeries.coeff_one_mul (φ := Bexp) (ψ := Binvexp) (R := ℂ))
  have hexpr :
      PowerSeries.coeff 1 Bexp * PowerSeries.constantCoeff Binvexp +
          PowerSeries.coeff 1 Binvexp * PowerSeries.constantCoeff Bexp = 0 := by
    simpa [hformula] using hcoeff1
  -- Solve for the unknown coefficient.
  -- Everything else is explicit.
  have hccinv : PowerSeries.constantCoeff Binvexp = (1 : ℂ) / 1728 := by
    -- This is the same as the `coeff 0` computation.
    -- `constantCoeff` is `coeff 0`.
    calc
      PowerSeries.constantCoeff Binvexp = PowerSeries.coeff 0 Binvexp := by
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      _ = (1 : ℂ) / 1728 := coeff_Binv_expected_0
  -- Turn `hexpr` into a concrete numerical equation.
  have : PowerSeries.coeff 1 Binvexp = (1 : ℂ) / 72 := by
    -- `(-41472) * (1/1728) + (coeff 1 Binvexp) * 1728 = 0`.
    have hb1 : PowerSeries.coeff 1 Bexp = (-41472 : ℂ) := by
      simpa [Bexp] using coeff_B_expected_1
    have hlin := hexpr
    -- Avoid `simp` unfolding `Bexp` into its definition; rewrite explicitly.
    rw [hb1, hccinv, constantCoeff_Bexp] at hlin
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    -- Rearrange and divide by `1728`.
    have hmul' :
        PowerSeries.coeff 1 Binvexp * (1728 : ℂ) =
          -((-41472 : ℂ) * ((1 : ℂ) / 1728)) := by
      -- `a + b = 0` implies `b = -a`.
      exact eq_neg_of_add_eq_zero_right hlin
    have hmul'' :
        PowerSeries.coeff 1 Binvexp * (1728 : ℂ) =
          (41472 : ℂ) * ((1 : ℂ) / 1728) := by
      simpa [neg_mul, neg_neg] using hmul'
    have hdiv := congrArg (fun z : ℂ => z * ((1728 : ℂ)⁻¹)) hmul''
    -- `(c * 1728) * 1728⁻¹ = c`.
    have : PowerSeries.coeff 1 Binvexp = (41472 : ℂ) * ((1 : ℂ) / 1728) * ((1728 : ℂ)⁻¹) := by
      simpa [mul_assoc, h1728] using hdiv
    -- Pure numeric evaluation.
    simpa [one_div] using (this.trans (by norm_num))
  simpa using this

private lemma coeff_Binv_expected_2 : PowerSeries.coeff 2 Binvexp = ((3 : ℂ) / 16) := by
  have hmul : Bexp * Binvexp = (1 : PowerSeries ℂ) := by
    simpa [Bexp, Binvexp] using
      (PowerSeries.mul_inv_cancel (φ := Bexp) (h := constCoeff_B_expected_ne_zero))
  have hcoeff2 : PowerSeries.coeff 2 (Bexp * Binvexp) = 0 := by
    have := congrArg (fun s : PowerSeries ℂ => PowerSeries.coeff 2 s) hmul
    simpa [PowerSeries.coeff_one] using this
  have hformula := coeff_mul_two Bexp Binvexp
  have hexpr :
      PowerSeries.coeff 0 Bexp * PowerSeries.coeff 2 Binvexp +
          PowerSeries.coeff 1 Bexp * PowerSeries.coeff 1 Binvexp +
        PowerSeries.coeff 2 Bexp * PowerSeries.coeff 0 Binvexp = 0 := by
    simpa [hformula] using hcoeff2
  have hb0 : PowerSeries.coeff 0 Bexp = (1728 : ℂ) := by
    simpa [Bexp] using coeff_B_expected_0
  have hb1 : PowerSeries.coeff 1 Bexp = (-41472 : ℂ) := by
    simpa [Bexp] using coeff_B_expected_1
  have hb2 : PowerSeries.coeff 2 Bexp = (435456 : ℂ) := by
    simpa [Bexp] using coeff_B_expected_2
  have hc0 : PowerSeries.coeff 0 Binvexp = (1 : ℂ) / 1728 := coeff_Binv_expected_0
  have hc1 : PowerSeries.coeff 1 Binvexp = (1 : ℂ) / 72 := coeff_Binv_expected_1
  have : PowerSeries.coeff 2 Binvexp = (3 : ℂ) / 16 := by
    have hlin := hexpr
    rw [hb0, hb1, hb2, hc0, hc1] at hlin
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    have hgroup :
        (1728 : ℂ) * PowerSeries.coeff 2 Binvexp +
            ((-41472 : ℂ) * ((1 : ℂ) / 72) + (435456 : ℂ) * ((1 : ℂ) / 1728)) = 0 := by
      simpa [add_assoc] using hlin
    have hmul' :
        (1728 : ℂ) * PowerSeries.coeff 2 Binvexp =
          -(((-41472 : ℂ) * ((1 : ℂ) / 72)) + (435456 : ℂ) * ((1 : ℂ) / 1728)) := by
      exact eq_neg_of_add_eq_zero_left hgroup
    have hdiv := congrArg (fun z : ℂ => ((1728 : ℂ)⁻¹) * z) hmul'
    have : PowerSeries.coeff 2 Binvexp =
        (1728 : ℂ)⁻¹ *
          (-(((-41472 : ℂ) * ((1 : ℂ) / 72)) + (435456 : ℂ) * ((1 : ℂ) / 1728))) := by
      simpa [mul_assoc, h1728] using hdiv
    simpa [one_div] using (this.trans (by norm_num))
  simpa using this

private lemma coeff_Binv_expected_3 : PowerSeries.coeff 3 Binvexp = ((50 : ℂ) / 27) := by
  have hmul : Bexp * Binvexp = (1 : PowerSeries ℂ) := by
    simpa [Bexp, Binvexp] using
      (PowerSeries.mul_inv_cancel (φ := Bexp) (h := constCoeff_B_expected_ne_zero))
  have hcoeff3 : PowerSeries.coeff 3 (Bexp * Binvexp) = 0 := by
    have := congrArg (fun s : PowerSeries ℂ => PowerSeries.coeff 3 s) hmul
    simpa [PowerSeries.coeff_one] using this
  have hformula := coeff_mul_three Bexp Binvexp
  have hexpr :
      PowerSeries.coeff 0 Bexp * PowerSeries.coeff 3 Binvexp +
          PowerSeries.coeff 1 Bexp * PowerSeries.coeff 2 Binvexp +
        PowerSeries.coeff 2 Bexp * PowerSeries.coeff 1 Binvexp +
      PowerSeries.coeff 3 Bexp * PowerSeries.coeff 0 Binvexp = 0 := by
    simpa [hformula] using hcoeff3
  have hb0 : PowerSeries.coeff 0 Bexp = (1728 : ℂ) := by
    simpa [Bexp] using coeff_B_expected_0
  have hb1 : PowerSeries.coeff 1 Bexp = (-41472 : ℂ) := by
    simpa [Bexp] using coeff_B_expected_1
  have hb2 : PowerSeries.coeff 2 Bexp = (435456 : ℂ) := by
    simpa [Bexp] using coeff_B_expected_2
  have hb3 : PowerSeries.coeff 3 Bexp = (-2543616 : ℂ) := by
    simpa [Bexp] using coeff_B_expected_3
  have hc0 : PowerSeries.coeff 0 Binvexp = (1 : ℂ) / 1728 := coeff_Binv_expected_0
  have hc1 : PowerSeries.coeff 1 Binvexp = (1 : ℂ) / 72 := coeff_Binv_expected_1
  have hc2 : PowerSeries.coeff 2 Binvexp = (3 : ℂ) / 16 := coeff_Binv_expected_2
  have : PowerSeries.coeff 3 Binvexp = (50 : ℂ) / 27 := by
    have hlin := hexpr
    rw [hb0, hb1, hb2, hb3, hc0, hc1, hc2] at hlin
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    have hgroup :
        (1728 : ℂ) * PowerSeries.coeff 3 Binvexp +
            ((-41472 : ℂ) * ((3 : ℂ) / 16) + (435456 : ℂ) * ((1 : ℂ) / 72) +
              (-2543616 : ℂ) * ((1 : ℂ) / 1728)) = 0 := by
      simpa [add_assoc] using hlin
    have hmul' :
        (1728 : ℂ) * PowerSeries.coeff 3 Binvexp =
          -(((-41472 : ℂ) * ((3 : ℂ) / 16)) + (435456 : ℂ) * ((1 : ℂ) / 72) +
              (-2543616 : ℂ) * ((1 : ℂ) / 1728)) := by
      exact eq_neg_of_add_eq_zero_left hgroup
    have hdiv := congrArg (fun z : ℂ => ((1728 : ℂ)⁻¹) * z) hmul'
    have : PowerSeries.coeff 3 Binvexp =
        (1728 : ℂ)⁻¹ *
          (-(((-41472 : ℂ) * ((3 : ℂ) / 16)) + (435456 : ℂ) * ((1 : ℂ) / 72) +
              (-2543616 : ℂ) * ((1 : ℂ) / 1728))) := by
      simpa [mul_assoc, h1728] using hdiv
    simpa [one_div] using (this.trans (by norm_num))
  simpa using this

private abbrev Nexp : PowerSeries ℂ := PowerSeries.C (1728 : ℂ) * (E4_q_expected ^ (3 : ℕ))
private abbrev Aexp : PowerSeries ℂ := kleinASeries E4_q_expected E6_q_expected

private lemma coeff_Nexp_0 : PowerSeries.coeff 0 Nexp = (1728 : ℂ) := by
  simp [Nexp, coeff_E4_cube_expected_0]

private lemma coeff_Nexp_1 : PowerSeries.coeff 1 Nexp = (1244160 : ℂ) := by
  simp [Nexp, coeff_E4_cube_expected_1]
  norm_num

private lemma coeff_Nexp_2 : PowerSeries.coeff 2 Nexp = (309795840 : ℂ) := by
  simp [Nexp, coeff_E4_cube_expected_2]
  norm_num

private lemma coeff_Nexp_3 : PowerSeries.coeff 3 Nexp = (29297479680 : ℂ) := by
  simp [Nexp, coeff_E4_cube_expected_3]
  norm_num

private lemma coeff_Aexp_0 : PowerSeries.coeff 0 Aexp = (1 : ℂ) := by
  -- `A = N * B⁻¹`.
  have h :
      PowerSeries.coeff 0 Aexp =
        PowerSeries.coeff 0 Nexp * PowerSeries.coeff 0 Binvexp := by
    -- Expand coefficient `0` of a product: only the `(0,0)` term contributes.
    simp [Aexp, kleinASeries, Nexp, Bexp, Binvexp, PowerSeries.coeff_mul]
  rw [h, coeff_Nexp_0, coeff_Binv_expected_0]
  norm_num

private lemma coeff_Aexp_1 : PowerSeries.coeff 1 Aexp = (744 : ℂ) := by
  -- `coeff 1 (N * B⁻¹) = n1*b0 + n0*b1`.
  have h :
      PowerSeries.coeff 1 Aexp =
        PowerSeries.coeff 0 Nexp * PowerSeries.coeff 1 Binvexp +
          PowerSeries.coeff 1 Nexp * PowerSeries.coeff 0 Binvexp := by
    simp [Aexp, kleinASeries, Nexp, Bexp, Binvexp, coeff_mul_one]
  -- Evaluate.
  -- Avoid `simp` linter churn: rewrite explicitly.
  rw [h, coeff_Nexp_0, coeff_Nexp_1, coeff_Binv_expected_0, coeff_Binv_expected_1]
  norm_num

private lemma coeff_Aexp_2 : PowerSeries.coeff 2 Aexp = (196884 : ℂ) := by
  have h :
      PowerSeries.coeff 2 Aexp =
        PowerSeries.coeff 0 Nexp * PowerSeries.coeff 2 Binvexp +
          PowerSeries.coeff 1 Nexp * PowerSeries.coeff 1 Binvexp +
          PowerSeries.coeff 2 Nexp * PowerSeries.coeff 0 Binvexp := by
    simpa [Aexp, kleinASeries, mul_assoc, Nexp, Bexp, Binvexp] using (coeff_mul_two Nexp Binvexp)
  rw [h, coeff_Nexp_0, coeff_Nexp_1, coeff_Nexp_2, coeff_Binv_expected_0, coeff_Binv_expected_1,
    coeff_Binv_expected_2]
  norm_num

private lemma coeff_Aexp_3 : PowerSeries.coeff 3 Aexp = (21493760 : ℂ) := by
  have h :
      PowerSeries.coeff 3 Aexp =
        PowerSeries.coeff 0 Nexp * PowerSeries.coeff 3 Binvexp +
          PowerSeries.coeff 1 Nexp * PowerSeries.coeff 2 Binvexp +
          PowerSeries.coeff 2 Nexp * PowerSeries.coeff 1 Binvexp +
          PowerSeries.coeff 3 Nexp * PowerSeries.coeff 0 Binvexp := by
    simpa [Aexp, kleinASeries, mul_assoc, Nexp, Bexp, Binvexp] using (coeff_mul_three Nexp Binvexp)
  rw [h, coeff_Nexp_0, coeff_Nexp_1, coeff_Nexp_2, coeff_Nexp_3, coeff_Binv_expected_0,
    coeff_Binv_expected_1, coeff_Binv_expected_2, coeff_Binv_expected_3]
  norm_num

/-!
### Laurent coefficients: expected series matches `J_q`
-/

private lemma coeff_kleinJ_qLaurent_expected (n : ℕ) :
    (kleinJ_qLaurent E4_q_expected E6_q_expected).coeff ((n : ℤ) + (-1 : ℤ)) =
      PowerSeries.coeff n Aexp := by
  -- Use `coeff_single_mul_add` for the `q^{-1}` shift.
  -- Note: `ofPowerSeries` is supported on nonnegative exponents.
  have hshift :
      ((HahnSeries.single (-1 : ℤ) (1 : ℂ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (kleinASeries E4_q_expected E6_q_expected)).coeff
          ((n : ℤ) + (-1 : ℤ)) =
        (HahnSeries.ofPowerSeries ℤ ℂ (kleinASeries E4_q_expected E6_q_expected)).coeff (n : ℤ) := by
    simpa using
      (HahnSeries.coeff_single_mul_add (r := (1 : ℂ))
        (x := HahnSeries.ofPowerSeries ℤ ℂ (kleinASeries E4_q_expected E6_q_expected))
        (a := (n : ℤ)) (b := (-1 : ℤ)))
  have hcoeff :
      (HahnSeries.ofPowerSeries ℤ ℂ (kleinASeries E4_q_expected E6_q_expected)).coeff (n : ℤ) =
        PowerSeries.coeff n (kleinASeries E4_q_expected E6_q_expected) := by
    -- This is the defining compatibility lemma for `ofPowerSeries`.
    simpa using
      (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (R := ℂ)
        (kleinASeries E4_q_expected E6_q_expected) n)
  have :
      (kleinJ_qLaurent E4_q_expected E6_q_expected).coeff ((n : ℤ) + (-1 : ℤ)) =
        PowerSeries.coeff n (kleinASeries E4_q_expected E6_q_expected) := by
    -- `kleinJ_qLaurent` is definitional and we avoid rewriting inside `ofPowerSeries`.
    simpa [kleinJ_qLaurent] using (hshift.trans hcoeff)
  simpa [Aexp] using this

theorem kleinJ₀_qLaurent_expected_coeff_neg1 :
    (kleinJ₀_qLaurent E4_q_expected E6_q_expected).coeff (-1) = (1 : ℂ) := by
  -- exponent `-1` corresponds to `n = 0` in the shifted power series.
  have hj : (kleinJ_qLaurent E4_q_expected E6_q_expected).coeff (-1) = PowerSeries.coeff 0 Aexp := by
    simpa using (coeff_kleinJ_qLaurent_expected (n := 0))
  -- subtracting `744` has no effect on exponent `-1`.
  simp [kleinJ₀_qLaurent, hj, coeff_Aexp_0]

theorem kleinJ₀_qLaurent_expected_coeff_0 :
    (kleinJ₀_qLaurent E4_q_expected E6_q_expected).coeff 0 = (0 : ℂ) := by
  have hj : (kleinJ_qLaurent E4_q_expected E6_q_expected).coeff 0 = PowerSeries.coeff 1 Aexp := by
    simpa using (coeff_kleinJ_qLaurent_expected (n := 1))
  -- exponent `0` is `n=1` after shifting, and then we subtract `744`.
  simp [kleinJ₀_qLaurent, hj, coeff_Aexp_1]

theorem kleinJ₀_qLaurent_expected_coeff_1 :
    (kleinJ₀_qLaurent E4_q_expected E6_q_expected).coeff 1 = (firstJCoeff : ℂ) := by
  have hj : (kleinJ_qLaurent E4_q_expected E6_q_expected).coeff 1 = PowerSeries.coeff 2 Aexp := by
    simpa using (coeff_kleinJ_qLaurent_expected (n := 2))
  simp [kleinJ₀_qLaurent, hj, coeff_Aexp_2, HeytingLean.Moonshine.firstJCoeff]

theorem kleinJ₀_qLaurent_expected_coeff_2 :
    (kleinJ₀_qLaurent E4_q_expected E6_q_expected).coeff 2 = (secondJCoeff : ℂ) := by
  have hj : (kleinJ_qLaurent E4_q_expected E6_q_expected).coeff 2 = PowerSeries.coeff 3 Aexp := by
    simpa using (coeff_kleinJ_qLaurent_expected (n := 3))
  simp [kleinJ₀_qLaurent, hj, coeff_Aexp_3, HeytingLean.Moonshine.secondJCoeff]

theorem kleinJ₀_qLaurent_expected_coeffs_match_J_q :
    (kleinJ₀_qLaurent E4_q_expected E6_q_expected).coeff (-1) = J_q.coeff (-1) ∧
    (kleinJ₀_qLaurent E4_q_expected E6_q_expected).coeff 0 = J_q.coeff 0 ∧
    (kleinJ₀_qLaurent E4_q_expected E6_q_expected).coeff 1 = J_q.coeff 1 ∧
    (kleinJ₀_qLaurent E4_q_expected E6_q_expected).coeff 2 = J_q.coeff 2 := by
  constructor
  · simpa [coeff_J_q_neg1] using kleinJ₀_qLaurent_expected_coeff_neg1
  constructor
  · simpa [coeff_J_q_0] using kleinJ₀_qLaurent_expected_coeff_0
  constructor
  · simpa [coeff_J_q_1] using kleinJ₀_qLaurent_expected_coeff_1
  · simpa [coeff_J_q_2] using kleinJ₀_qLaurent_expected_coeff_2

/-!
### Transfer to the true `qExpansion₁` series via Item 1 equalities
-/

theorem kleinJ₀_qLaurent_qExpansion₁_coeffs_match_J_q :
    (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff (-1) = J_q.coeff (-1) ∧
    (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 0 = J_q.coeff 0 ∧
    (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 1 = J_q.coeff 1 ∧
    (kleinJ₀_qLaurent (qExpansion₁ E4) (qExpansion₁ E6)).coeff 2 = J_q.coeff 2 := by
  -- Rewrite the input power series to the expected ones.
  simpa [qExpansion₁_E4_eq_expected, qExpansion₁_E6_eq_expected] using
    kleinJ₀_qLaurent_expected_coeffs_match_J_q

end HeytingLean.Moonshine.Modular
