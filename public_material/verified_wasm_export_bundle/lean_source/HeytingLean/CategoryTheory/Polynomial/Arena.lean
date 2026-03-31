/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Polynomial Arenas and Dynamics
==============================

This module connects polynomial functors to arena semantics and dynamical systems.

## Main Definitions

* `Arena` - A polynomial functor viewed as an interactive system
* `ArenaStep` - State transition in an arena
* `ArenaCoalgebra` - Coalgebraic dynamics on arenas
* `ArenaWiring` - Parallel and sequential composition of arenas

## Mathematical Background

An arena is a polynomial functor interpreted as an interactive system:
- Positions = states of the system
- Directions = actions/observations available at each state

The dynamics arise from polynomial coalgebras:
- A coalgebra `α : S → P(S)` unfolds to an infinite behavior tree
- This connects to Para bicategory dynamics via ParaHom semantics

## References

* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf) Ch. 5
* [nLab: Arena](https://ncatlab.org/nlab/show/arena)
* CDL/Para bicategory connection
-/

import HeytingLean.CategoryTheory.Polynomial.Basic
import HeytingLean.CategoryTheory.Polynomial.Substitution

namespace HeytingLean.CategoryTheory.Polynomial

open _root_.CategoryTheory.Polynomial

universe u v

/-! ## Arena Basics -/

/-- An arena is a polynomial functor viewed as an interactive system.

In game semantics:
- Positions = player positions (states)
- Directions = opponent moves (actions) at each position

In dynamical systems:
- Positions = system states
- Directions = observations/interfaces at each state -/
abbrev Arena := Poly

/-! ## Arena Step Function -/

/-- A step function for an arena.

Given current state and an action, produces the next state.
This is a "Moore machine" interpretation of the arena. -/
structure ArenaStep (A : Poly) where
  /-- Current state -/
  state : A.pos
  /-- Action taken -/
  action : A.dir state
  /-- Next state -/
  next : A.pos

/-- Run one step of an arena with a transition function. -/
def arenaStep (A : Poly) (trans : (s : A.pos) → A.dir s → A.pos)
    (s : A.pos) (a : A.dir s) : A.pos :=
  trans s a

/-! ## Arena Coalgebras (Dynamics) -/

/-- An arena coalgebra defines infinite behavior.

Given `α : S → A(S)` where `A` is an arena, we get:
- For each state `s : S`, a position `α(s).1 : A.pos`
- A continuation map `α(s).2 : A.dir (α(s).1) → S`

This is the "behavior" of the system: at each state, we see a position
and can follow any direction to the next state. -/
structure ArenaCoalgebra (A : Poly) where
  /-- State space -/
  State : Type*
  /-- Coalgebra structure: state → arena applied to state -/
  unfold : State → applyFun A State

namespace ArenaCoalgebra

variable {A : Poly}

/-- Get the arena position at a state -/
def position (c : ArenaCoalgebra A) (s : c.State) : A.pos :=
  (c.unfold s).1

/-- Get the continuation at a state for a given direction -/
def continue_ (c : ArenaCoalgebra A) (s : c.State) (d : A.dir (c.position s)) : c.State :=
  (c.unfold s).2 d

/-- Run n steps of a coalgebra from initial state with a strategy -/
def runN (c : ArenaCoalgebra A) (strategy : (s : c.State) → A.dir (c.position s))
    (init : c.State) : ℕ → c.State
  | 0 => init
  | n + 1 => c.continue_ (c.runN strategy init n) (strategy (c.runN strategy init n))

end ArenaCoalgebra

/-! ## Arena Morphisms as System Simulations -/

/-- A morphism of arenas is a simulation between interactive systems.

Given arenas `A` and `B`, a morphism `f : A ⟶ B` provides:
- Forward simulation: each A-position gives a B-position
- Backward action translation: B-actions can be simulated by A-actions -/
def arenaSimulation {A B : Poly} (f : A ⟶ B) (s : A.pos) :
    -- A simulation relates positions and translates actions
    Σ (t : B.pos), B.dir t → A.dir s :=
  ⟨f.onPos s, f.onDir s⟩

/-- Coalgebra morphism (simulation between dynamical systems) -/
structure CoalgebraMorphism {A : Poly} (c d : ArenaCoalgebra A) where
  /-- State mapping -/
  stateMap : c.State → d.State
  /-- Preserves coalgebra structure -/
  preserve : ∀ s, (d.unfold (stateMap s)).1 = (c.unfold s).1

/-! ## Arena Wiring (Composition) -/

/-- Parallel composition of arenas.

Two systems running in parallel:
- States are pairs of states
- Actions are pairs of actions -/
def arenaParallel (A B : Poly) : Poly where
  pos := A.pos × B.pos
  dir := fun ⟨a, b⟩ => A.dir a × B.dir b

infixl:70 " ⊗ₐ " => arenaParallel

/-- Sequential composition via substitution.

System B feeds into system A:
- Uses the substitution monoidal product from Polynomial.Substitution -/
def arenaSequential (A B : Poly) : Poly :=
  subst A B

infixl:60 " ◁ₐ " => arenaSequential

/-! ## Connection to Globular Structures -/

/-- An arena defines a 1-dimensional globular structure.

Positions = 0-cells (objects)
Directions = 1-cells (morphisms from each object)

Higher-dimensional structure arises from iterated arenas. -/
structure ArenaGlobular (A : Poly) where
  /-- 0-cells are positions -/
  zero_cells : A.pos
  /-- 1-cells at a 0-cell are directions -/
  one_cells : (x : A.pos) → A.dir x
  /-- Source of a 1-cell (default: return the source position) -/
  src : (x : A.pos) → A.dir x → A.pos := fun x _ => x
  /-- Target requires an arena step function -/
  tgt : (x : A.pos) → A.dir x → A.pos

/-- Iterated arenas for higher globular structure.

Arena^n where we iterate the construction n times. -/
def arenaIterate (A : Poly) : ℕ → Poly
  | 0 => poly1  -- Terminal arena
  | n + 1 => subst A (arenaIterate A n)

/-! ## Para Connection -/

/-- The connection between arenas and Para morphisms.

A ParaHom X Y with parameter P is equivalent to an arena coalgebra where:
- States = P
- Arena positions = dependent on the output type
- The dynamics come from para composition -/
def arenaFromParaShape (P X : Type*) : Poly :=
  monomial P X

/-- Arena step from Para semantics.

Given a ParaHom with f : P × X → Y, the arena step at state p with input x gives f(p,x). -/
def paraAsArenaStep (P X Y : Type*) (f : P × X → Y) (p : P) (x : X) : Y :=
  f (p, x)

end HeytingLean.CategoryTheory.Polynomial
