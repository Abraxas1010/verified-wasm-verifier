import HeytingLean.Moonshine.Modular.Eisenstein
import Mathlib.NumberTheory.ArithmeticFunction

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open scoped BigOperators

/-!
Expected `q`-expansions for the normalized level-1 Eisenstein modular forms `E4` and `E6`.

These are the classical formulas:
- `E4(q) = 1 + 240 * ∑_{n≥1} σ₃(n) q^n`
- `E6(q) = 1 - 504 * ∑_{n≥1} σ₅(n) q^n`

Mathlib currently defines `ModularForm.E` analytically as a convergent Eisenstein series, and
provides `qExpansion` for all modular forms (as the Taylor series of the cusp function), but
does not yet prove these explicit coefficient identities (see the note in
`Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean`).

This file is kernel-pure scaffolding: it packages the expected power series and proves small,
purely algebraic coefficient computations that we will later use once we prove
`qExpansion₁ E4 = E4_q_expected` and `qExpansion₁ E6 = E6_q_expected`.
-/

private def sigma (k n : ℕ) : ℕ :=
  ArithmeticFunction.sigma k n

private lemma sigma_one (k : ℕ) : sigma k 1 = 1 := by
  simp [sigma, ArithmeticFunction.sigma_one]

private lemma sigma_two_pow (k : ℕ) : sigma k 2 = 1 + 2 ^ k := by
  -- `2 = 2^1` and `σ_k(p^i) = ∑_{j=0..i} p^(j*k)`.
  have hp : Nat.Prime 2 := by decide
  -- Use the prime-power formula directly and let `simp` evaluate the tiny sum.
  simpa [sigma, pow_one, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.zero_mul, Nat.one_mul] using
    (ArithmeticFunction.sigma_apply_prime_pow (k := k) (p := 2) (i := 1) hp)

private lemma sigma_three_pow (k : ℕ) : sigma k 3 = 1 + 3 ^ k := by
  have hp : Nat.Prime 3 := by decide
  simpa [sigma, pow_one, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.zero_mul, Nat.one_mul] using
    (ArithmeticFunction.sigma_apply_prime_pow (k := k) (p := 3) (i := 1) hp)

private lemma sigma_four_pow (k : ℕ) : sigma k 4 = 1 + 2 ^ k + 2 ^ (2 * k) := by
  -- `4 = 2^2`.
  have hp : Nat.Prime 2 := by decide
  -- Use the prime-power formula and let `simp` evaluate the length-3 sum.
  simpa [sigma, pow_two, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.zero_mul, Nat.one_mul, Nat.two_mul] using
    (ArithmeticFunction.sigma_apply_prime_pow (k := k) (p := 2) (i := 2) hp)

/-- The expected `q`-expansion of `E4` as a `PowerSeries`. -/
noncomputable def E4_q_expected : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    if n = 0 then (1 : ℂ) else (240 : ℂ) * (sigma 3 n : ℂ)

/-- The expected `q`-expansion of `E6` as a `PowerSeries`. -/
noncomputable def E6_q_expected : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    if n = 0 then (1 : ℂ) else (-504 : ℂ) * (sigma 5 n : ℂ)

@[simp] lemma E4_q_expected_coeff_zero : (E4_q_expected.coeff 0) = (1 : ℂ) := by
  simp [E4_q_expected]

@[simp] lemma E6_q_expected_coeff_zero : (E6_q_expected.coeff 0) = (1 : ℂ) := by
  simp [E6_q_expected]

lemma E4_q_expected_coeff_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (E4_q_expected.coeff n) = (240 : ℂ) * (ArithmeticFunction.sigma 3 n : ℂ) := by
  simp [E4_q_expected, hn, sigma]

lemma E6_q_expected_coeff_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (E6_q_expected.coeff n) = (-504 : ℂ) * (ArithmeticFunction.sigma 5 n : ℂ) := by
  simp [E6_q_expected, hn, sigma]

@[simp] lemma E4_q_expected_coeff_one : (E4_q_expected.coeff 1) = (240 : ℂ) := by
  simp [E4_q_expected, sigma_one]

@[simp] lemma E6_q_expected_coeff_one : (E6_q_expected.coeff 1) = (-504 : ℂ) := by
  simp [E6_q_expected, sigma_one]

@[simp] lemma E4_q_expected_coeff_two : (E4_q_expected.coeff 2) = (2160 : ℂ) := by
  -- `σ₃(2) = 1 + 2^3 = 9`.
  have hs : sigma 3 2 = 9 := by
    calc
      sigma 3 2 = 1 + 2 ^ 3 := sigma_two_pow 3
      _ = 9 := by decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_two : (E6_q_expected.coeff 2) = (-16632 : ℂ) := by
  -- `σ₅(2) = 1 + 2^5 = 33`.
  have hs : sigma 5 2 = 33 := by
    calc
      sigma 5 2 = 1 + 2 ^ 5 := sigma_two_pow 5
      _ = 33 := by decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_three : (E4_q_expected.coeff 3) = (6720 : ℂ) := by
  -- `σ₃(3) = 1 + 3^3 = 28`.
  have hs : sigma 3 3 = 28 := by
    calc
      sigma 3 3 = 1 + 3 ^ 3 := sigma_three_pow 3
      _ = 28 := by decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_three : (E6_q_expected.coeff 3) = (-122976 : ℂ) := by
  -- `σ₅(3) = 1 + 3^5 = 244`.
  have hs : sigma 5 3 = 244 := by
    calc
      sigma 5 3 = 1 + 3 ^ 5 := sigma_three_pow 5
      _ = 244 := by decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_four : (E4_q_expected.coeff 4) = (17520 : ℂ) := by
  -- `σ₃(4) = 1 + 2^3 + 2^(2*3) = 73`.
  have hs : sigma 3 4 = 73 := by
    calc
      sigma 3 4 = 1 + 2 ^ 3 + 2 ^ (2 * 3) := sigma_four_pow 3
      _ = 73 := by decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_four : (E6_q_expected.coeff 4) = (-532728 : ℂ) := by
  -- `σ₅(4) = 1 + 2^5 + 2^(2*5) = 1057`.
  have hs : sigma 5 4 = 1057 := by
    calc
      sigma 5 4 = 1 + 2 ^ 5 + 2 ^ (2 * 5) := sigma_four_pow 5
      _ = 1057 := by decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_five : (E4_q_expected.coeff 5) = (30240 : ℂ) := by
  have hs : sigma 3 5 = 126 := by native_decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_five : (E6_q_expected.coeff 5) = (-1575504 : ℂ) := by
  have hs : sigma 5 5 = 3126 := by native_decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_six : (E4_q_expected.coeff 6) = (60480 : ℂ) := by
  have hs : sigma 3 6 = 252 := by native_decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_six : (E6_q_expected.coeff 6) = (-4058208 : ℂ) := by
  have hs : sigma 5 6 = 8052 := by native_decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_seven : (E4_q_expected.coeff 7) = (82560 : ℂ) := by
  have hs : sigma 3 7 = 344 := by native_decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_seven : (E6_q_expected.coeff 7) = (-8471232 : ℂ) := by
  have hs : sigma 5 7 = 16808 := by native_decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_eight : (E4_q_expected.coeff 8) = (140400 : ℂ) := by
  have hs : sigma 3 8 = 585 := by native_decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_eight : (E6_q_expected.coeff 8) = (-17047800 : ℂ) := by
  have hs : sigma 5 8 = 33825 := by native_decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_nine : (E4_q_expected.coeff 9) = (181680 : ℂ) := by
  have hs : sigma 3 9 = 757 := by native_decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_nine : (E6_q_expected.coeff 9) = (-29883672 : ℂ) := by
  have hs : sigma 5 9 = 59293 := by native_decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_ten : (E4_q_expected.coeff 10) = (272160 : ℂ) := by
  have hs : sigma 3 10 = 1134 := by native_decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_ten : (E6_q_expected.coeff 10) = (-51991632 : ℂ) := by
  have hs : sigma 5 10 = 103158 := by native_decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_eleven : (E4_q_expected.coeff 11) = (319680 : ℂ) := by
  have hs : sigma 3 11 = 1332 := by native_decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_eleven : (E6_q_expected.coeff 11) = (-81170208 : ℂ) := by
  have hs : sigma 5 11 = 161052 := by native_decide
  simp [E6_q_expected, hs]
  norm_num

@[simp] lemma E4_q_expected_coeff_twelve : (E4_q_expected.coeff 12) = (490560 : ℂ) := by
  have hs : sigma 3 12 = 2044 := by native_decide
  simp [E4_q_expected, hs]
  norm_num

@[simp] lemma E6_q_expected_coeff_twelve : (E6_q_expected.coeff 12) = (-129985632 : ℂ) := by
  have hs : sigma 5 12 = 257908 := by native_decide
  simp [E6_q_expected, hs]
  norm_num

/-!
Minimal algebra for the denominator `E4^3 - E6^2` at low order.

Classically `E4^3 - E6^2 = 1728 * Δ`, and `Δ` has leading term `q`. The next lemma is the purely
formal coefficient computation that the `q^1` coefficient of `E4_q_expected^3 - E6_q_expected^2`
is `1728`. This is enough to show (once we have equality with the true `qExpansion`) that
`kleinJ` has a simple pole at infinity.
-/

lemma coeff_one_E4_q_expected_pow_three : PowerSeries.coeff 1 (E4_q_expected ^ (3 : ℕ)) = (720 : ℂ) := by
  -- With `E4 = 1 + 240 q + ...`, the `q^1` coefficient of `E4^3` is `3 * 240 = 720`.
  -- Use `PowerSeries.coeff_one_pow`.
  have h := (PowerSeries.coeff_one_pow (R := ℂ) (n := 3) E4_q_expected)
  -- Rewrite `constantCoeff` as `coeff 0` so we can reuse our coefficient lemmas.
  have hc : PowerSeries.constantCoeff E4_q_expected = PowerSeries.coeff 0 E4_q_expected := by
    simpa using
      (PowerSeries.coeff_zero_eq_constantCoeff_apply (R := ℂ) (φ := E4_q_expected)).symm
  have h' :
      PowerSeries.coeff 1 (E4_q_expected ^ (3 : ℕ)) =
        (3 : ℂ) * (240 : ℂ) * (1 : ℂ) ^ 2 := by
    simpa [hc, E4_q_expected_coeff_zero, E4_q_expected_coeff_one] using h
  have : (3 : ℂ) * (240 : ℂ) * (1 : ℂ) ^ 2 = (720 : ℂ) := by norm_num
  simpa using h'.trans this

lemma coeff_one_E6_q_expected_pow_two : PowerSeries.coeff 1 (E6_q_expected ^ (2 : ℕ)) = (-1008 : ℂ) := by
  -- With `E6 = 1 - 504 q + ...`, the `q^1` coefficient of `E6^2` is `2 * (-504) = -1008`.
  have h := (PowerSeries.coeff_one_pow (R := ℂ) (n := 2) E6_q_expected)
  have hc : PowerSeries.constantCoeff E6_q_expected = PowerSeries.coeff 0 E6_q_expected := by
    simpa using
      (PowerSeries.coeff_zero_eq_constantCoeff_apply (R := ℂ) (φ := E6_q_expected)).symm
  have h' :
      PowerSeries.coeff 1 (E6_q_expected ^ (2 : ℕ)) =
        (2 : ℂ) * (-504 : ℂ) * (1 : ℂ) ^ 1 := by
    simpa [hc, E6_q_expected_coeff_zero, E6_q_expected_coeff_one] using h
  have : (2 : ℂ) * (-504 : ℂ) * (1 : ℂ) ^ 1 = (-1008 : ℂ) := by norm_num
  simpa using h'.trans this

lemma coeff_one_E4_cubed_sub_E6_sq_expected :
    PowerSeries.coeff 1 (E4_q_expected ^ (3 : ℕ) - E6_q_expected ^ (2 : ℕ)) = (1728 : ℂ) := by
  -- Coefficients are linear, so `coeff 1 (f - g) = coeff 1 f - coeff 1 g`.
  simp [sub_eq_add_neg, coeff_one_E4_q_expected_pow_three, coeff_one_E6_q_expected_pow_two]
  norm_num

end HeytingLean.Moonshine.Modular
