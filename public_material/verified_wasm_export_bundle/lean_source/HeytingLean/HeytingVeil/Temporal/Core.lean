/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

/-!
# HeytingVeil Temporal Core

A minimal temporal-semantics kernel for HeytingVeil:
- traces,
- transition systems,
- safety/liveness predicates,
- weak/strong fairness schemata.

This file is intentionally lightweight and proof-escape free.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Temporal

universe u

abbrev Trace (State : Type u) := Nat → State

structure Machine (State : Type u) where
  Init : State → Prop
  Step : State → State → Prop

variable {State : Type u}

/-- A trace is valid for machine `M` if it starts in `Init` and each adjacent pair follows `Step`. -/
def ValidTrace (M : Machine State) (σ : Trace State) : Prop :=
  M.Init (σ 0) ∧ ∀ n : Nat, M.Step (σ n) (σ (n + 1))

/-- `Enabled R s` means there exists a successor state via relation `R`. -/
def Enabled (R : State → State → Prop) (s : State) : Prop :=
  ∃ t : State, R s t

/-- A stutter step at index `n` repeats the same state. -/
def Stutter (σ : Trace State) (n : Nat) : Prop :=
  σ (n + 1) = σ n

/-- Safety predicate: an invariant holds at every trace position. -/
def Safety (Inv : State → Prop) (σ : Trace State) : Prop :=
  ∀ n : Nat, Inv (σ n)

/-- Eventuality over natural indices. -/
def Eventually (P : Nat → Prop) : Prop :=
  ∃ n : Nat, P n

/-- Infinitely often over natural indices. -/
def InfinitelyOften (P : Nat → Prop) : Prop :=
  ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ P m

/-- Weak fairness schema for transition relation `R` along trace `σ`. -/
def WeakFair (R : State → State → Prop) (σ : Trace State) : Prop :=
  InfinitelyOften (fun n => Enabled R (σ n)) →
    InfinitelyOften (fun n => R (σ n) (σ (n + 1)))

/-- Strong fairness schema for transition relation `R` along trace `σ`. -/
def StrongFair (R : State → State → Prop) (σ : Trace State) : Prop :=
  (∀ n : Nat, ∃ m : Nat, n ≤ m ∧ ∃ k : Nat, m ≤ k ∧ Enabled R (σ k)) →
    InfinitelyOften (fun n => R (σ n) (σ (n + 1)))

@[simp] theorem validTrace_init {M : Machine State} {σ : Trace State}
    (h : ValidTrace M σ) : M.Init (σ 0) :=
  h.1

@[simp] theorem validTrace_step {M : Machine State} {σ : Trace State}
    (h : ValidTrace M σ) (n : Nat) : M.Step (σ n) (σ (n + 1)) :=
  h.2 n

@[simp] theorem safety_at {Inv : State → Prop} {σ : Trace State}
    (h : Safety Inv σ) (n : Nat) : Inv (σ n) :=
  h n

end Temporal
end HeytingVeil
end HeytingLean
