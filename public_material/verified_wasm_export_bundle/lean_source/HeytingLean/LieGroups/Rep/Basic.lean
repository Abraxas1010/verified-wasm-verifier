/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.LieGroups.Imports

/-!
# Group Representations — Basic Utilities

This module provides utilities for group representations, including
invariant subspaces and equivariant maps.

## Main definitions

* `IsInvariant` — predicate for invariant vectors
* `invariantsSubmodule` — the submodule of invariant vectors
* `IsEquivariant` — predicate for equivariant linear maps

## Main results

* `invariant_apply` — invariant vectors are fixed by the representation
-/

set_option autoImplicit false

namespace HeytingLean
namespace LieGroups
namespace Rep

section Basic

variable {k : Type*} [CommSemiring k]
variable {G : Type*} [Group G]

variable {V : Type*} [AddCommMonoid V] [Module k V]

/-- The submodule of invariant vectors (mathlib's `Representation.invariants`). -/
noncomputable def invariantsSubmodule (ρ : Representation k G V) : Submodule k V :=
  ρ.invariants

@[simp] lemma mem_invariantsSubmodule (ρ : Representation k G V) (v : V) :
    v ∈ invariantsSubmodule (ρ := ρ) ↔ ∀ g : G, ρ g v = v := by
  simp [invariantsSubmodule, Representation.mem_invariants]

/-- Membership lemma: if `v` is invariant, then `ρ g v = v`. -/
lemma invariant_apply {ρ : Representation k G V} {v : V}
    (hv : v ∈ invariantsSubmodule ρ) (g : G) :
    ρ g v = v :=
  (mem_invariantsSubmodule (ρ := ρ) v).1 hv g

/-- The trivial vector `0` is always invariant. -/
lemma zero_invariant (ρ : Representation k G V) : (0 : V) ∈ invariantsSubmodule ρ :=
  (invariantsSubmodule ρ).zero_mem

/-- Invariant vectors are closed under addition. -/
lemma add_invariant {ρ : Representation k G V} {v w : V}
    (hv : v ∈ invariantsSubmodule ρ) (hw : w ∈ invariantsSubmodule ρ) :
    v + w ∈ invariantsSubmodule ρ :=
  (invariantsSubmodule ρ).add_mem hv hw

end Basic

section Equivariance

variable {k : Type*} [CommSemiring k]
variable {G : Type*} [Monoid G]

variable {V : Type*} [AddCommMonoid V] [Module k V]
variable {W : Type*} [AddCommMonoid W] [Module k W]

/-- Equivariance between representations. -/
def IsEquivariant (ρ : Representation k G V) (ρ' : Representation k G W) (f : V →ₗ[k] W) : Prop :=
  ∀ g v, f (ρ g v) = ρ' g (f v)

/-- The zero map is equivariant. -/
lemma isEquivariant_zero (ρ : Representation k G V) (ρ' : Representation k G W) :
    IsEquivariant ρ ρ' 0 := by
  intro g v
  simp

/-- Composition of equivariant maps is equivariant. -/
lemma IsEquivariant.comp {U : Type*} [AddCommMonoid U] [Module k U]
    {ρ : Representation k G V} {ρ' : Representation k G W} {ρ'' : Representation k G U}
    {f : V →ₗ[k] W} {g : W →ₗ[k] U}
    (hf : IsEquivariant ρ ρ' f) (hg : IsEquivariant ρ' ρ'' g) :
    IsEquivariant ρ ρ'' (g.comp f) := by
  intro h v
  simp [hf h v, hg h (f v)]

end Equivariance

end Rep
end LieGroups
end HeytingLean
