import HeytingLean.Moonshine.Modular.KleinCuspLaurentBridge
import HeytingLean.Moonshine.Modular.KleinJ0Laurent

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

/-!
## Explicit Low-Order Coefficients for `kleinDps` / `kleinBps`

These are reusable coefficient facts for the denominator-side power series:

- `kleinDps = (qExpansion₁ E4)^3 - (qExpansion₁ E6)^2`
- `kleinBps` is the shifted series of `kleinDps`.

They are extracted from the expected-series computations in `KleinJ0Laurent.lean`
and transported to the actual `qExpansion₁` forms via
`qExpansion₁_E4_eq_expected` / `qExpansion₁_E6_eq_expected`.
-/

lemma kleinDps_coeff_two : kleinDps.coeff 2 = (-41472 : ℂ) := by
  simpa [kleinDps, qExpansion₁_E4_eq_expected, qExpansion₁_E6_eq_expected] using
    coeff_kleinDSeries_expected_2

lemma kleinDps_coeff_three : kleinDps.coeff 3 = (435456 : ℂ) := by
  simpa [kleinDps, qExpansion₁_E4_eq_expected, qExpansion₁_E6_eq_expected] using
    coeff_kleinDSeries_expected_3

lemma kleinDps_coeff_four : kleinDps.coeff 4 = (-2543616 : ℂ) := by
  simpa [kleinDps, qExpansion₁_E4_eq_expected, qExpansion₁_E6_eq_expected] using
    coeff_kleinDSeries_expected_4

lemma kleinBps_coeff_one : kleinBps.coeff 1 = (-41472 : ℂ) := by
  simpa [kleinBps, qExpansion₁_E4_eq_expected, qExpansion₁_E6_eq_expected] using
    coeff_kleinBSeries_expected_1

lemma kleinBps_coeff_two : kleinBps.coeff 2 = (435456 : ℂ) := by
  simpa [kleinBps, qExpansion₁_E4_eq_expected, qExpansion₁_E6_eq_expected] using
    coeff_kleinBSeries_expected_2

lemma kleinBps_coeff_three : kleinBps.coeff 3 = (-2543616 : ℂ) := by
  simpa [kleinBps, qExpansion₁_E4_eq_expected, qExpansion₁_E6_eq_expected] using
    coeff_kleinBSeries_expected_3

lemma norm_kleinBps_coeff_one : ‖kleinBps.coeff 1‖ = (41472 : ℝ) := by
  rw [kleinBps_coeff_one]
  norm_num

lemma norm_kleinBps_coeff_two : ‖kleinBps.coeff 2‖ = (435456 : ℝ) := by
  rw [kleinBps_coeff_two]
  norm_num

lemma norm_kleinBps_coeff_three : ‖kleinBps.coeff 3‖ = (2543616 : ℝ) := by
  rw [kleinBps_coeff_three]
  norm_num

end HeytingLean.Moonshine.Modular
