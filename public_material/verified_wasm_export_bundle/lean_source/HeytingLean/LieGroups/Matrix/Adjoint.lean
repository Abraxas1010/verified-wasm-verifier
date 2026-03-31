/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.LieGroups.Matrix.GLExp

/-!
# Adjoint Action on Matrices

This module defines the adjoint action of GL(n) on matrices (conjugation)
and proves compatibility with the exponential map.

## Main definitions

* `Ad` — conjugation action `A ↦ g A g⁻¹` as a linear map

## Main results

* `exp_Ad` — exponential respects conjugation: `exp(Ad g A) = g (exp A) g⁻¹`
-/

set_option autoImplicit false

open NormedSpace -- for `exp`

namespace HeytingLean
namespace LieGroups
namespace MatrixLie

section Adjoint

variable {𝕜 : Type*} [RCLike 𝕜]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation action `A ↦ g A g⁻¹` as a `𝕜`-linear map. -/
noncomputable def Ad (g : GL ι 𝕜) : Matrix ι ι 𝕜 →ₗ[𝕜] Matrix ι ι 𝕜 where
  toFun A := (g : Matrix ι ι 𝕜) * A * (g⁻¹ : GL ι 𝕜)
  map_add' A B := by
    simp only [mul_add, add_mul]
  map_smul' c A := by
    simp [mul_assoc]

/-- Ad is a group action. -/
lemma Ad_one : Ad (1 : GL ι 𝕜) = LinearMap.id := by
  ext A
  simp [Ad]

lemma Ad_mul (g h : GL ι 𝕜) : Ad (g * h) = (Ad g).comp (Ad h) := by
  ext A
  simp [Ad, LinearMap.comp_apply, mul_assoc]

/-- Exponential respects conjugation by units. -/
theorem exp_Ad (g : GL ι 𝕜) (A : Matrix ι ι 𝕜) :
    exp 𝕜 (Ad g A) =
      (g : Matrix ι ι 𝕜) * exp 𝕜 A * ((g⁻¹ : GL ι 𝕜) : Matrix ι ι 𝕜) := by
  simpa [Ad] using (Matrix.exp_units_conj (𝕂 := 𝕜) (U := (g : (Matrix ι ι 𝕜)ˣ)) A)

end Adjoint

end MatrixLie
end LieGroups
end HeytingLean
