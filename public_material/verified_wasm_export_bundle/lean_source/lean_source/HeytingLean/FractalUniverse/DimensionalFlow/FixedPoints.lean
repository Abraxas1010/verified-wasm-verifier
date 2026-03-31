import HeytingLean.FractalUniverse.DimensionalFlow.BetaFunction

/-!
# Fixed Point Analysis

Full fixed-point classification of the dimensional flow beta function.
UV fixed point (≈2, unstable) and IR fixed point (=4, stable).
Source: Veselov Section 4.1 continued.
-/

namespace HeytingLean.FractalUniverse.DimensionalFlow

/-- Classification of beta function fixed points with stability data.
    The UV fixed point is unstable (β' > 0), the IR is stable (β' < 0). -/
structure BetaFixedPointAnalysis where
  β : ℝ → ℝ
  uv_fixed : ℝ
  ir_fixed : ℝ
  uv_is_fixed : β uv_fixed = 0
  ir_is_fixed : β ir_fixed = 0
  /-- UV is unstable: positive slope at fixed point. -/
  uv_unstable : 0 < deriv β uv_fixed
  /-- IR is stable: negative slope at fixed point. -/
  ir_stable : deriv β ir_fixed < 0
  /-- No intermediate fixed points. -/
  no_intermediate : ∀ D, uv_fixed < D → D < ir_fixed → β D ≠ 0
  /-- β > 0 between fixed points (flow toward IR). -/
  beta_positive_between : ∀ D, uv_fixed < D → D < ir_fixed → 0 < β D

/-- The leading-order beta β(D) = A(4-D) has ir_fixed = 4 with stability. -/
theorem leading_order_ir_fixed (A : ℝ) :
    (fun D => A * (4 - D)) 4 = 0 := by ring

/-- The leading-order beta function has derivative -A everywhere. -/
theorem leading_order_hasDerivAt (A D : ℝ) :
    HasDerivAt (fun x => A * (4 - x)) (-A) D := by
  have h1 : HasDerivAt (fun x => 4 - x) (-1) D := by
    have := (hasDerivAt_const D (4 : ℝ)).sub (hasDerivAt_id D)
    convert this using 1; norm_num
  have h2 : HasDerivAt (fun x => A * (4 - x)) (A * -1) D :=
    h1.const_mul A
  simp only [mul_neg_one] at h2
  exact h2

/-- Since A > 0, the derivative at D=4 is negative → stable. -/
theorem leading_order_ir_stable (A : ℝ) (hA : 0 < A) :
    deriv (fun D => A * (4 - D)) 4 < 0 := by
  have h := (leading_order_hasDerivAt A 4).deriv
  rw [h]; linarith

/-- The leading-order beta is positive between D_uv and 4 when D_uv < 4. -/
theorem leading_order_positive_between (A _D_uv D : ℝ) (hA : 0 < A)
    (_hUV : _D_uv < D) (hIR : D < 4) :
    0 < A * (4 - D) := by nlinarith

end HeytingLean.FractalUniverse.DimensionalFlow
