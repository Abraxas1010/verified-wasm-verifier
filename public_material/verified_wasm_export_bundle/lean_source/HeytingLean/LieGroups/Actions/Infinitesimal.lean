/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.LieGroups.Basic
import HeytingLean.LieGroups.Actions.SmoothAction

/-!
# Infinitesimal Actions

This module defines the infinitesimal action of a Lie algebra on a manifold,
derived from a smooth group action.

## Main definitions

* `orbitMap` — the orbit map `g ↦ g • x` for fixed `x`
* `infinitesimalAt` — derivative of orbit map at identity: `𝔤 → T_x M`
* `fundamental` — fundamental vector field: `X ↦ (x ↦ infinitesimalAt x X)`

## Main results

* `contMDiff_orbitMap` — the orbit map is smooth
* `fundamental_add` — fundamental vector fields are linear in the generator
-/

set_option autoImplicit false

open scoped Manifold

namespace HeytingLean
namespace LieGroups

section Infinitesimal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace 𝕜 E_G]
variable {H_G : Type*} [TopologicalSpace H_G]
variable (I_G : ModelWithCorners 𝕜 E_G H_G)

variable {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace 𝕜 E_M]
variable {H_M : Type*} [TopologicalSpace H_M]
variable (I_M : ModelWithCorners 𝕜 E_M H_M)

variable {n : ℕ∞}

variable (G : Type*) [TopologicalSpace G] [ChartedSpace H_G G] [Group G]
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H_M M]

variable [MulAction G M]
variable [ContMDiffMulAction I_G I_M n G M]

/-- Orbit map at `x`: `g ↦ g • x`. -/
def orbitMap (x : M) : G → M := fun g => g • x

/-- The orbit map is smooth. -/
lemma contMDiff_orbitMap (x : M) : ContMDiff I_G I_M n (orbitMap G M x) :=
  contMDiff_smul_const I_G I_M n G M x

/--
Infinitesimal action at `x`:
the derivative at the identity of the orbit map.

This maps Lie algebra elements to tangent vectors at `x`.
-/
noncomputable def infinitesimalAt (x : M) :
    GroupLieAlgebra I_G G →L[𝕜] TangentSpace I_M x := by
  have h : orbitMap G M x 1 = x := one_smul G x
  exact h ▸ mfderiv I_G I_M (orbitMap G M x) 1

/-- Fundamental vector field associated to `X`, as a pointwise tangent vector. -/
noncomputable def fundamental (X : GroupLieAlgebra I_G G) : (x : M) → TangentSpace I_M x :=
  fun x => infinitesimalAt I_G I_M G M x X

/-- Fundamental vector fields are additive in the generator. -/
lemma fundamental_add (X Y : GroupLieAlgebra I_G G) (x : M) :
    fundamental I_G I_M G M (X + Y) x =
    fundamental I_G I_M G M X x + fundamental I_G I_M G M Y x := by
  simp only [fundamental]
  exact map_add (infinitesimalAt I_G I_M G M x) X Y

/-- Fundamental vector fields are homogeneous in the generator. -/
lemma fundamental_smul (c : 𝕜) (X : GroupLieAlgebra I_G G) (x : M) :
    fundamental I_G I_M G M (c • X) x = c • fundamental I_G I_M G M X x := by
  simp only [fundamental]
  exact map_smul (infinitesimalAt I_G I_M G M x) c X

end Infinitesimal

end LieGroups
end HeytingLean
