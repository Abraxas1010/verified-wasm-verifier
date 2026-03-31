/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.SurrealLie.FormalLieGroup
import HeytingLean.SurrealLie.Flows

/-!
# Kernel Lie Action Trait

This module provides an agent-facing abstraction for Lie algebra actions on states,
suitable for use in kernel/program verification contexts.

## Main definitions

* `KernelLieAction` — typeclass bundling group, algebra, exp, and state action
* `flowAct` — derived action via flow
* `InvariantUnderFlow` — predicate stable under all flows

## Design

This is the "API surface" for coding agents to interact with the Surreal Lie machinery.
The key operations are:
- `flowAct X t s` — apply flow for time `t` in direction `X` to state `s`
- `InvariantUnderFlow P` — check if property `P` is preserved by all flows
-/

set_option autoImplicit false

namespace HeytingLean.SurrealLie

/-! ### Kernel Lie Action Typeclass -/

/-- A Lie action on a state space, suitable for kernel/agent use.
    Provides group `G`, algebra `𝔤`, exponential, and action on states. -/
class KernelLieAction (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (State : Type*) where
  /-- The Lie group. -/
  G : Type*
  /-- Group structure. -/
  instGroup : Group G
  /-- The Lie algebra. -/
  𝔤 : Type*
  /-- Additive group on algebra. -/
  instAddCommGroup : AddCommGroup 𝔤
  /-- Module structure. -/
  instModule : Module 𝕜 𝔤
  /-- Exponential map. -/
  exp : 𝔤 → G
  /-- Exp at zero is identity. -/
  exp_zero : exp 0 = 1
  /-- Group action on states. -/
  act : G → State → State
  /-- Identity acts trivially. -/
  act_one : ∀ s, act 1 s = s
  /-- Action is compatible. -/
  act_mul : ∀ g h s, act (g * h) s = act g (act h s)

attribute [instance] KernelLieAction.instGroup KernelLieAction.instAddCommGroup
  KernelLieAction.instModule

namespace KernelLieAction

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {State : Type*} [KernelLieAction 𝕜 State]

/-- Flow action: apply exponential of scaled generator to state. -/
def flowAct (X : 𝔤 (𝕜 := 𝕜) (State := State)) (t : 𝕜) (s : State) : State :=
  act (exp (t • X)) s

/-- Flow at zero is identity. -/
@[simp] lemma flowAct_zero (X : 𝔤 (𝕜 := 𝕜) (State := State)) (s : State) :
    flowAct X 0 s = s := by
  simp only [flowAct, zero_smul, exp_zero, act_one]

/-- Predicate: property is invariant under all flows. -/
def InvariantUnderFlow (P : State → Prop) : Prop :=
  ∀ X : 𝔤 (𝕜 := 𝕜) (State := State), ∀ t : 𝕜, ∀ s : State, P s → P (flowAct X t s)

/-- Predicate: property is infinitesimally stable in direction X. -/
def InfinitesimallyStable (P : State → Prop) (X : 𝔤 (𝕜 := 𝕜) (State := State)) : Prop :=
  ∀ ε : 𝕜, IsInfinitesimal ε → ∀ s : State, P s → P (flowAct X ε s)

/-- Flow invariance implies infinitesimal stability. -/
lemma invariantUnderFlow_implies_infinitesimallyStable
    {P : State → Prop} (hP : InvariantUnderFlow (𝕜 := 𝕜) P)
    (X : 𝔤 (𝕜 := 𝕜) (State := State)) :
    InfinitesimallyStable P X := by
  intro ε _ s hs
  exact hP X ε s hs

/-- Conjunction of invariant properties is invariant. -/
lemma invariantUnderFlow_and {P Q : State → Prop}
    (hP : InvariantUnderFlow (𝕜 := 𝕜) P) (hQ : InvariantUnderFlow (𝕜 := 𝕜) Q) :
    InvariantUnderFlow (𝕜 := 𝕜) (fun s => P s ∧ Q s) := by
  intro X t s ⟨hp, hq⟩
  exact ⟨hP X t s hp, hQ X t s hq⟩

/-- Constant true is invariant. -/
lemma invariantUnderFlow_true : InvariantUnderFlow (𝕜 := 𝕜) (State := State) (fun _ => True) := by
  intro _ _ _ _
  trivial

end KernelLieAction

/-! ### Query Interface for Agents -/

/-- Check if moving state `s` by infinitesimal `ε` in direction `X` preserves `P`. -/
def checkInfinitesimalStability {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {State : Type*} [KernelLieAction 𝕜 State]
    (P : State → Prop) [DecidablePred P]
    (X : KernelLieAction.𝔤 (𝕜 := 𝕜) (State := State))
    (ε : 𝕜) (s : State) : Bool :=
  P s && P (KernelLieAction.flowAct X ε s)

end HeytingLean.SurrealLie
