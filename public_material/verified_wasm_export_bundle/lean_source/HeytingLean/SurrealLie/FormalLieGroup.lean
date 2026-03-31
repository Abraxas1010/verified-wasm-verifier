/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Order.Field.Basic
import HeytingLean.SurrealLie.Scale

/-!
# Formal Lie Group Structure

This module defines a formal/algebraic Lie group structure that works
over non-Archimedean fields without requiring topology.

## Main definitions

* `FormalLieGroup` — structure bundling `G`, `𝔤`, `exp`, `log` with axioms
* `flow` — one-parameter subgroup `t ↦ exp(t • X)`

## Design Notes

The `Small` predicate captures "neighborhood of identity" without topology.
For nilpotent matrix Lie algebras, this is exact (finite polynomial exp).
-/

set_option autoImplicit false

namespace HeytingLean.SurrealLie

/-- A formal Lie group structure over an ordered field.
    No topology required - uses algebraic `Small` predicate. -/
structure FormalLieGroup (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] where
  /-- The group. -/
  G : Type*
  /-- Group structure on `G`. -/
  instGroup : Group G
  /-- The Lie algebra. -/
  𝔤 : Type*
  /-- Lie ring structure on `𝔤`. -/
  instLieRing : LieRing 𝔤
  /-- Lie algebra structure on `𝔤`. -/
  instLieAlgebra : LieAlgebra 𝕜 𝔤
  /-- Exponential map from algebra to group. -/
  exp : 𝔤 → G
  /-- Logarithm map from group to algebra. -/
  log : G → 𝔤
  /-- Smallness predicate (replaces topology). -/
  Small : 𝔤 → Prop
  /-- Zero is small. -/
  small_zero : Small 0
  /-- Smallness is closed under negation. -/
  small_neg : ∀ X, Small X → Small (-X)
  /-- Small elements are closed under scaling by infinitesimals. -/
  small_smul_infinitesimal :
    ∀ X, Small X → ∀ ε : 𝕜, IsInfinitesimal (𝕜 := 𝕜) ε → Small (ε • X)
  /-- Exponential of zero is the identity. -/
  exp_zero : exp 0 = 1
  /-- Log-exp identity on small elements. -/
  log_exp : ∀ X, Small X → log (exp X) = X
  /-- Exp-add identity for commuting small elements. -/
  exp_add_of_comm : ∀ X Y, Small X → Small Y → ⁅X, Y⁆ = 0 → exp (X + Y) = exp X * exp Y

attribute [instance] FormalLieGroup.instGroup FormalLieGroup.instLieRing FormalLieGroup.instLieAlgebra

namespace FormalLieGroup

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- One-parameter flow for a fixed generator. -/
def flow (L : FormalLieGroup 𝕜) (X : L.𝔤) : 𝕜 → L.G :=
  fun t => L.exp (t • X)

/-- Flow at zero is the identity. -/
@[simp] lemma flow_zero (L : FormalLieGroup 𝕜) (X : L.𝔤) :
    L.flow X 0 = 1 := by
  simp [flow, L.exp_zero]

/-- Flow addition law (requires smallness and commutativity). -/
lemma flow_add (L : FormalLieGroup 𝕜) (X : L.𝔤) (t s : 𝕜)
    (ht : L.Small (t • X)) (hs : L.Small (s • X)) :
    L.flow X (t + s) = L.flow X t * L.flow X s := by
  simp only [flow, add_smul]
  apply L.exp_add_of_comm
  · exact ht
  · exact hs
  · -- Bracket of scalar multiples of same element is zero
    calc
      ⁅t • X, s • X⁆ = t • ⁅X, s • X⁆ := by
        exact smul_lie (t := t) (x := X) (m := s • X)
      _ = t • (s • ⁅X, X⁆) := by
        simp [lie_smul]
      _ = t • (s • 0) := by
        simp [lie_self]
      _ = 0 := by
        simp

/-- `exp (-X)` is the inverse of `exp X` whenever both `X` and `-X` are small.

This is derived from `exp_add_of_comm` plus `exp_zero`, not an extra postulate. -/
lemma exp_neg_of_small (L : FormalLieGroup 𝕜) (X : L.𝔤)
    (hX : L.Small X) (hneg : L.Small (-X)) :
    L.exp (-X) = (L.exp X)⁻¹ := by
  have hbr : ⁅X, -X⁆ = 0 := by
    -- Use scalar bilinearity: `-X = (-1) • X`.
    calc
      ⁅X, -X⁆ = ⁅X, (-1 : 𝕜) • X⁆ := by
        simp
      _ = (-1 : 𝕜) • ⁅X, X⁆ := by
        exact lie_smul (t := (-1 : 𝕜)) (x := X) (m := X)
      _ = 0 := by
        simp [lie_self]
  have hmul : L.exp X * L.exp (-X) = 1 := by
    have h := L.exp_add_of_comm X (-X) hX hneg hbr
    -- Rewrite `exp (X + -X)` to `1` using `exp_zero`.
    simpa [L.exp_zero] using h.symm
  have := congrArg (fun g => (L.exp X)⁻¹ * g) hmul
  simpa [mul_assoc] using this

/-- Infinitesimal flow stays near identity. -/
lemma flow_infinitesimal (L : FormalLieGroup 𝕜) (X : L.𝔤) (hX : L.Small X)
    (ε : 𝕜) (hε : IsInfinitesimal (𝕜 := 𝕜) ε) :
    L.Small (ε • X) :=
  L.small_smul_infinitesimal X hX ε hε

end FormalLieGroup

end HeytingLean.SurrealLie
