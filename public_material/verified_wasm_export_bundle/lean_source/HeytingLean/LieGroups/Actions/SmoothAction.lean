/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.LieGroups.Imports

/-!
# Smooth Group Actions on Manifolds

This module defines `ContMDiffMulAction`, a mixin class expressing that a group action
`G ⟶ M` is smooth (C^n) as a map `G × M → M`.

## Main definitions

* `ContMDiffMulAction` — the action map is `ContMDiff`

## Main results

* `contMDiff_smul` — the global action map is smooth
* `contMDiff_const_smul` — for fixed `g`, the map `x ↦ g • x` is smooth
* `contMDiff_smul_const` — for fixed `x`, the map `g ↦ g • x` is smooth
-/

set_option autoImplicit false

open scoped Manifold

namespace HeytingLean
namespace LieGroups

section SmoothAction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace 𝕜 E_G]
variable {H_G : Type*} [TopologicalSpace H_G]
variable (I_G : ModelWithCorners 𝕜 E_G H_G)

variable {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace 𝕜 E_M]
variable {H_M : Type*} [TopologicalSpace H_M]
variable (I_M : ModelWithCorners 𝕜 E_M H_M)

variable (n : ℕ∞)

variable (G : Type*) [TopologicalSpace G] [ChartedSpace H_G G] [Group G]
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H_M M]

variable [MulAction G M]

/-- Mixin: the action map `G × M → M` is `C^n`. -/
class ContMDiffMulAction : Prop where
  contMDiff_smul :
    ContMDiff (I_G.prod I_M) I_M n (fun p : G × M => p.1 • p.2)

/-- Helper: the global action map is smooth. -/
lemma contMDiff_smul [ContMDiffMulAction I_G I_M n G M] :
    ContMDiff (I_G.prod I_M) I_M n (fun p : G × M => p.1 • p.2) :=
  ContMDiffMulAction.contMDiff_smul

/-- For fixed `g`, the map `x ↦ g • x` is `C^n`. -/
  lemma contMDiff_const_smul [ContMDiffMulAction I_G I_M n G M] (g : G) :
      ContMDiff I_M I_M n (fun x : M => g • x) := by
    have hpair : ContMDiff I_M (I_G.prod I_M) n (fun x : M => (g, x)) :=
    contMDiff_const.prodMk contMDiff_id
    exact (contMDiff_smul I_G I_M n G M).comp hpair

/-- For fixed `x`, the map `g ↦ g • x` is `C^n`. -/
  lemma contMDiff_smul_const [ContMDiffMulAction I_G I_M n G M] (x : M) :
      ContMDiff I_G I_M n (fun g : G => g • x) := by
    have hpair : ContMDiff I_G (I_G.prod I_M) n (fun g : G => (g, x)) :=
    contMDiff_id.prodMk contMDiff_const
    exact (contMDiff_smul I_G I_M n G M).comp hpair

end SmoothAction

end LieGroups
end HeytingLean
