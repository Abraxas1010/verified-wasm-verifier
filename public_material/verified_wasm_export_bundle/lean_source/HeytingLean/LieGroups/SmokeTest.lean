/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.LieGroups.Basic
import HeytingLean.LieGroups.Actions.SmoothAction
import HeytingLean.LieGroups.Actions.Infinitesimal
import HeytingLean.LieGroups.Matrix.GLExp
import HeytingLean.LieGroups.Matrix.Adjoint
import HeytingLean.LieGroups.Measure.HaarAveraging
import HeytingLean.LieGroups.Rep.Basic
import HeytingLean.LieGroups.RootSystems.Bridge

/-!
# Lie Groups Utility Stack — Smoke Tests

This module provides smoke tests that verify the Lie Group utility stack
compiles and the main theorems typecheck.

## Tests

1. Inversion is smooth in a Lie group
2. Orbit map is smooth under `ContMDiffMulAction`
3. One-parameter subgroup laws for matrices
4. Exponential respects conjugation
5. Haar measure invariance
6. Representation invariants
-/

set_option autoImplicit false

open scoped Manifold
open NormedSpace -- for `exp`

namespace HeytingLean
namespace LieGroups

/-! ### Lie Group Smoothness -/

section Smoke_LieGroup

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)
variable {n : WithTop ℕ∞}

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G]
variable [Fact (minSmoothness 𝕜 3 ≤ n)]

-- Ensure the `minSmoothness`-level Lie group instance is available to build the Lie bracket.
local instance : LieGroup I (minSmoothness 𝕜 3) G :=
  LieGroup.of_le (I := I) (G := G) (m := minSmoothness 𝕜 3) (n := n)
    (by simpa using (inferInstance : Fact (minSmoothness 𝕜 3 ≤ n)).out)

example : LieRing (GroupLieAlgebra I G) := by
  infer_instance

example : LieAlgebra 𝕜 (GroupLieAlgebra I G) := by
  infer_instance

example : ContMDiff I I n (fun g : G => g⁻¹) :=
by
  simpa using (LieGroups.contMDiff_inv (I := I) (n := n) (G := G))

example : ContMDiff (I.prod I) I n (fun p : G × G => p.1 * p.2) :=
by
  simpa using (LieGroups.contMDiff_mul (I := I) (n := n) (G := G))

end Smoke_LieGroup

/-! ### Smooth Actions -/

section Smoke_Action

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

-- orbit map is smooth
example (x : M) : ContMDiff I_G I_M n (orbitMap G M x) :=
  contMDiff_orbitMap I_G I_M G M x

-- fixed-g action is smooth
example (g : G) : ContMDiff I_M I_M n (fun x : M => g • x) :=
  contMDiff_const_smul I_G I_M n G M g

-- fixed-x action is smooth
example (x : M) : ContMDiff I_G I_M n (fun g : G => g • x) :=
  contMDiff_smul_const I_G I_M n G M x

end Smoke_Action

/-! ### Matrix Exponential -/

section Smoke_Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open MatrixLie

-- one-parameter subgroup at zero
example (A : Matrix ι ι 𝕜) : oneParam A 0 = 1 :=
  oneParam_zero A

-- one-parameter subgroup addition law
example (A : Matrix ι ι 𝕜) (t s : 𝕜) :
    oneParam A (t + s) = oneParam A t * oneParam A s :=
  oneParam_add A t s

-- exponential respects conjugation
example (g : GL ι 𝕜) (A : Matrix ι ι 𝕜) :
    exp 𝕜 (Ad g A) =
      (g : Matrix ι ι 𝕜) * exp 𝕜 A * ((g⁻¹ : GL ι 𝕜) : Matrix ι ι 𝕜) :=
  exp_Ad g A

end Smoke_Matrix

/-! ### Haar Measure -/

section Smoke_Measure

open MeasureTheory
open Measure
open scoped Pointwise

variable {G : Type*} [Group G]
variable {α : Type*} [MeasurableSpace α] [MulAction G α]

variable (μ : MeasureTheory.Measure α) [SMulInvariantMeasure G α μ]

example (g : G) {s : Set α} (hs : μ s = 0) : μ (g • s) = 0 :=
  smul_null μ g hs

end Smoke_Measure

/-! ### Representations -/

section Smoke_Rep

open Rep

variable {k : Type*} [CommSemiring k]
variable {G : Type*} [Group G]
variable {V : Type*} [AddCommMonoid V] [Module k V]

variable (ρ : Representation k G V)
variable (v : V)

example (hv : v ∈ invariantsSubmodule ρ) (g : G) : ρ g v = v :=
  invariant_apply hv g

example : (0 : V) ∈ invariantsSubmodule ρ :=
  zero_invariant ρ

end Smoke_Rep

/-! ### Root systems bridge -/

section Smoke_RootSystems

-- The bridge module is import-only for now; this checks it remains build-clean.
example : True := by
  trivial

end Smoke_RootSystems

end LieGroups
end HeytingLean
