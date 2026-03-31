import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import HeytingLean.Constructor.Core

/-
# Constructor Theory core (substrates, variables, tasks)

Minimal, substrate‑agnostic core for Constructor Theory inside `HeytingLean`.

This file defines:
* `Attribute`  : sets of substrate states;
* `Variable`   : finite families of attributes with a basic disjointness condition;
* `Task`       : finite collections of input/output attribute pairs;
* `Task.seq`   : serial composition (list concatenation, laws live in the nucleus layer);
* `Task.par`   : parallel composition (same carrier as `seq`, semantics deferred);
* `Constructor`: abstract device that can enact tasks on a substrate.

The goal is to provide lightweight syntax that other modules (CT nucleus,
information, thermodynamics, bridges) can reuse without committing to a
particular physical substrate.
-/

namespace HeytingLean
namespace Constructor
namespace CT

open Classical

universe u

/-- A CT attribute is a set of states of a substrate `σ`. -/
abbrev Attribute (σ : Type u) : Type u :=
  Set σ

/-- A CT variable is a finite family of attributes together with a
pairwise‑disjointness condition.  The exact covering and exhaustiveness
properties are deferred to concrete substrates. -/
structure Variable (σ : Type u) where
  /-- List of attributes that make up the variable. -/
  attrs : List (Attribute σ)
  /-- Attributes indexed by distinct positions in the list do not overlap. -/
  pairwiseDisjoint :
    ∀ {i j}
      (hi : i < attrs.length)
      (hj : j < attrs.length),
      i ≠ j →
      Disjoint (attrs.get ⟨i, hi⟩) (attrs.get ⟨j, hj⟩)

/-- A CT task over a substrate `σ`: a finite collection of input/output
attribute pairs.  Semantics are provided by substrate‑specific models. -/
structure Task (σ : Type u) where
  arcs : List (Attribute σ × Attribute σ)

namespace Task

variable {σ : Type u}

/-- Serial composition of tasks: at the syntactic level this is just list
concatenation.  Algebraic laws connecting this to semantics live in the
CT nucleus and substrate adapters. -/
def seq (T U : Task σ) : Task σ :=
  ⟨T.arcs ++ U.arcs⟩

/-- Parallel composition of tasks: we reuse the same carrier as serial
composition (list concatenation).  Substrate‑specific models may give
different semantics to `seq` and `par`. -/
def par (T U : Task σ) : Task σ :=
  ⟨T.arcs ++ U.arcs⟩

end Task

/-- An abstract constructor over a substrate `σ`.  The predicate
`canEnact` marks the tasks that the constructor can realise with
arbitrarily high accuracy and reliability. -/
structure Constructor (σ : Type u) where
  canEnact : Task σ → Prop

/-- A small adapter linking CT tasks over a substrate `σ` into an ambient
nucleus `R` on a complete lattice `α`.  This relates CT‑level enactability
to the generic `Constructor.possible` predicate from the meta‑theory. -/
structure Model (σ : Type u) {α : Type v} [CompleteLattice α]
    (R : Nucleus α) where
  /-- Encoding of CT tasks as ambient task‑expressions. -/
  encode : Task σ → α
  /-- Underlying constructor on the CT substrate. -/
  ctor : Constructor σ
  /-- Soundness: if the constructor can enact a task, its encoding is
  globally possible for the nucleus `R`. -/
  sound :
    ∀ {T : Task σ}, ctor.canEnact T →
      _root_.HeytingLean.Constructor.possible R (encode T)

namespace Examples

/-- A trivial attribute on `Bool` selecting the `true` state. -/
def boolAttrTrue : Attribute Bool :=
  {b | b = true}

/-- A trivial attribute on `Bool` selecting the `false` state. -/
def boolAttrFalse : Attribute Bool :=
  {b | b = false}

/-- Empty variable: a degenerate variable over any substrate where the
attribute list is empty and the disjointness condition holds vacuously. -/
def emptyVariable (σ : Type u) : Variable σ where
  attrs := []
  pairwiseDisjoint := by
    intro i j hi hj hneq
    exact (Nat.not_lt_zero _ hi).elim

/-- A syntactic task over `Bool` that swaps the `true`/`false` attributes.
The semantics of this task are substrate‑dependent and not fixed here. -/
def swapTaskBool : Task Bool :=
  { arcs := [(boolAttrFalse, boolAttrTrue), (boolAttrTrue, boolAttrFalse)] }

/-- A trivial constructor that can enact every task.  This is useful as a
dummy substrate instance when wiring CT syntax into tests or examples. -/
def trivialConstructor (σ : Type u) : Constructor σ :=
  { canEnact := fun _ => True }

end Examples

end CT
end Constructor
end HeytingLean
