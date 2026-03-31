/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.LieGroups.Imports
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix Exponential and One-Parameter Subgroups

This module provides the matrix exponential landing in `GL(n, 𝕜)` and
one-parameter subgroups for matrix Lie groups.

## Main definitions

* `GL` — abbreviation for `Matrix.GeneralLinearGroup`
* `GLExp` — matrix exponential into `GL`
* `oneParam` — one-parameter subgroup `𝕜 → GL` for a fixed generator

## Main results

* `coe_GLExp` — `GLExp A` coerces to `exp A` as a matrix
* `oneParam_add` — `oneParam A (t + s) = oneParam A t * oneParam A s`
* `oneParam_zero` — `oneParam A 0 = 1`
-/

set_option autoImplicit false

open scoped BigOperators

open NormedSpace -- for `exp`

namespace HeytingLean
namespace LieGroups
namespace MatrixLie

section GLExp

variable {𝕜 : Type*} [RCLike 𝕜]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix exponential lands in units (hence in GL).
    We use Mathlib's matrix exponential (`Matrix.isUnit_exp`) to avoid
    ad-hoc normed-algebra assumptions on `Matrix ι ι 𝕜`. -/
noncomputable def GLExp (A : Matrix ι ι 𝕜) : GL ι 𝕜 :=
  (Matrix.isUnit_exp (𝕂 := 𝕜) (A := A)).unit

/-- The underlying matrix of `GLExp A` is `exp A`. -/
@[simp] lemma coe_GLExp (A : Matrix ι ι 𝕜) :
    (GLExp (ι := ι) (𝕜 := 𝕜) A : Matrix ι ι 𝕜) = exp 𝕜 A :=
  (Matrix.isUnit_exp (𝕂 := 𝕜) (A := A)).unit_spec

/--
One-parameter subgroup for a fixed generator `A`.
Maps additive parameter `t` to `exp(t • A)` in GL.
-/
noncomputable def oneParam (A : Matrix ι ι 𝕜) : 𝕜 → GL ι 𝕜 :=
  fun t => GLExp (t • A)

@[simp] lemma oneParam_zero (A : Matrix ι ι 𝕜) : oneParam (ι := ι) (𝕜 := 𝕜) A 0 = 1 := by
  ext
  simp [oneParam, GLExp]

/-- One-parameter subgroup satisfies the group law. -/
lemma oneParam_add (A : Matrix ι ι 𝕜) (t s : 𝕜) :
    oneParam (ι := ι) (𝕜 := 𝕜) A (t + s) =
      oneParam (ι := ι) (𝕜 := 𝕜) A t * oneParam (ι := ι) (𝕜 := 𝕜) A s := by
  have hcomm : Commute (t • A) (s • A) :=
    ((Commute.refl A).smul_left t).smul_right s
  ext
  simp [oneParam, GLExp, add_smul, Matrix.exp_add_of_commute (𝕂 := 𝕜) _ _ hcomm]

/-- One-parameter subgroup is a monoid homomorphism from additive `𝕜`. -/
noncomputable def oneParamHom (A : Matrix ι ι 𝕜) : Multiplicative 𝕜 →* GL ι 𝕜 where
  toFun t := oneParam (ι := ι) (𝕜 := 𝕜) A t.toAdd
  map_one' := by simp [oneParam_zero]
  map_mul' t s := by
    -- `Multiplicative` turns `(*)` into `(+ )` on the underlying type.
    simpa [toAdd_mul] using (oneParam_add (ι := ι) (𝕜 := 𝕜) A t.toAdd s.toAdd)

end GLExp

end MatrixLie
end LieGroups
end HeytingLean
