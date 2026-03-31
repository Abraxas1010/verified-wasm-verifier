import HeytingLean.Moonshine.Modular.QParam
import HeytingLean.Moonshine.Modular.KleinCuspFunction
import HeytingLean.Moonshine.Modular.KleinCuspLaurentBridge
import HeytingLean.Moonshine.Modular.KleinDenominatorGlobalReduction

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

/-!
## Cusp-Coordinate Bridge for the Klein Denominator

This file relates the analytic function on `ℍ`

`kleinDenom τ = (E4 τ)^3 - (E6 τ)^2`

to the cusp-side expression in the `q`-parameter.

This does **not** prove global nonvanishing, but it makes the remaining obstruction explicit:
`kleinDenom τ ≠ 0` is equivalent to `kleinBfunExt (q τ) ≠ 0`.
-/

lemma kleinDenom_eq_kleinDfun (τ : ℍ) : kleinDenom τ = kleinDfun (q τ) := by
  -- `kleinDfun` is the cusp-side denominator `(E4_cusp q)^3 - (E6_cusp q)^2`.
  -- Rewrite `E4`/`E6` via their cusp functions.
  simp [kleinDenom, kleinDfun, q, ← E4_eq_E4_cusp, ← E6_eq_E6_cusp]

lemma kleinDenom_eq_q_mul_kleinBfunExt (τ : ℍ) :
    kleinDenom τ = q τ * kleinBfunExt (q τ) := by
  have hq : q τ ≠ 0 := q_ne_zero τ
  calc
    kleinDenom τ = kleinDfun (q τ) := kleinDenom_eq_kleinDfun (τ := τ)
    _ = q τ * kleinBfunExt (q τ) := by
          simpa using (kleinDfun_eq_mul_kleinBfunExt (q := q τ) hq)

lemma kleinDenom_ne_zero_iff_kleinBfunExt_ne_zero (τ : ℍ) :
    kleinDenom τ ≠ 0 ↔ kleinBfunExt (q τ) ≠ 0 := by
  have hq : q τ ≠ 0 := q_ne_zero τ
  constructor
  · intro hden hB
    -- If `kleinBfunExt (q τ) = 0`, then `kleinDenom τ = 0` by the cusp factorization.
    apply hden
    simp [kleinDenom_eq_q_mul_kleinBfunExt (τ := τ), hB]
  · intro hB hden
    -- If `kleinDenom τ = 0`, then `q τ * kleinBfunExt (q τ) = 0` and `q τ ≠ 0`.
    have : q τ * kleinBfunExt (q τ) = 0 := by
      simpa [kleinDenom_eq_q_mul_kleinBfunExt (τ := τ)] using hden
    have : kleinBfunExt (q τ) = 0 := by
      exact (mul_eq_zero.mp this).resolve_left hq
    exact hB this

end HeytingLean.Moonshine.Modular
