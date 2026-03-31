/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.SurrealLie.FormalLieGroup

/-!
# Flows and Counterfactual Reasoning

This module provides utilities for reasoning about flows (one-parameter subgroups)
and their use in counterfactual/perturbation analysis.

## Main definitions

* `ExpConnected` — relation capturing "connected via exp"
* `CounterfactualStable` — property stable under infinitesimal perturbation

## Philosophy

In Noneist logic, "gaps" are perturbations too small to see at the standard scale.
Flows provide a formal way to ask: "What happens if we nudge by an infinitesimal?"
-/

set_option autoImplicit false

namespace HeytingLean.SurrealLie

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### Exp-Connected Relation -/

/-- Two elements are exp-connected if one is reachable from the other via exp. -/
def ExpConnected (L : FormalLieGroup 𝕜) (g h : L.G) : Prop :=
  ∃ X : L.𝔤, L.Small X ∧ h = g * L.exp X

/-- Exp-connected is reflexive (via zero). -/
lemma expConnected_refl (L : FormalLieGroup 𝕜) (g : L.G) : ExpConnected L g g := by
  use 0
  constructor
  · exact L.small_zero
  · simp [L.exp_zero]

/-- Exp-connected is symmetric (via negation). -/
lemma expConnected_symm (L : FormalLieGroup 𝕜) {g h : L.G}
    (hgh : ExpConnected L g h) : ExpConnected L h g := by
  obtain ⟨X, hX, rfl⟩ := hgh
  refine ⟨-X, L.small_neg X hX, ?_⟩
  have hneg : L.Small (-X) := L.small_neg X hX
  have hexpneg : L.exp (-X) = (L.exp X)⁻¹ :=
    FormalLieGroup.exp_neg_of_small (L := L) X hX hneg
  simp [hexpneg, mul_assoc]

/-! ### Counterfactual Stability -/

/-- A predicate `P` on states is counterfactually stable at `s` under direction `X`
    if it remains true after infinitesimal perturbation. -/
def CounterfactualStable {State : Type*} (L : FormalLieGroup 𝕜)
    (act : L.G → State → State)
    (P : State → Prop) (s : State) (X : L.𝔤) : Prop :=
  ∀ ε : 𝕜, IsInfinitesimal (𝕜 := 𝕜) ε → P s → P (act (L.exp (ε • X)) s)

/-- Zero perturbation preserves stability. -/
lemma counterfactualStable_of_true {State : Type*} (L : FormalLieGroup 𝕜)
    (act : L.G → State → State)
    (hact : ∀ s, act 1 s = s)
    (P : State → Prop) (s : State) (X : L.𝔤) (hP : P s) :
    P (act (L.exp (0 • X)) s) := by
  simp [L.exp_zero, hact, hP]

/-! ### Infinitesimal Neighborhood -/

/-- The infinitesimal neighborhood of identity in `G`. -/
def InfinitesimalNbhd (L : FormalLieGroup 𝕜) : Set L.G :=
  { g |
    ∃ X : L.𝔤,
      L.Small X ∧ (∀ n : ℕ, 0 < n → ∃ ε : 𝕜, IsInfinitesimal (𝕜 := 𝕜) ε ∧ g = L.exp (ε • X)) }

/-- Identity is in infinitesimal neighborhood. -/
lemma one_mem_infinitesimalNbhd (L : FormalLieGroup 𝕜) :
    (1 : L.G) ∈ InfinitesimalNbhd L := by
  use 0
  constructor
  · exact L.small_zero
  · intro n _
    use 0
    constructor
    · exact isInfinitesimal_zero
    · simp [L.exp_zero]

end HeytingLean.SurrealLie
