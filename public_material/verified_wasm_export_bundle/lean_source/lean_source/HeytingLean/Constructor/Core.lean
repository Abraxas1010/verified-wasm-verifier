import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Nucleus
import Mathlib.Data.Multiset.Basic

/-!
# Constructor Core (meta-theory scaffold)

Abstract interface for Constructor Theory over a generic nucleus `R` on a
complete lattice. This file is intentionally substrate-agnostic and keeps all
laws lightweight enough to compile with `-Dno_sorry`.
-/

open Classical

namespace HeytingLean
namespace Constructor

universe u v

variable {α : Type u} [CompleteLattice α]

/-- A task-expression is globally possible for a nucleus `R` when it is not
annihilated to bottom by `R`. -/
def possible (R : Nucleus α) (a : α) : Prop :=
  R a ≠ ⊥

/-- A task-expression is globally impossible for a nucleus `R` when it is
sent to bottom by `R`. -/
def impossible (R : Nucleus α) (a : α) : Prop :=
  R a = ⊥

/-- No task-expression can be both globally possible and impossible for the
same nucleus. -/
lemma exclusive (R : Nucleus α) (a : α) :
    possible R a → ¬ impossible R a := by
  intro hPossible hImpossible
  exact hPossible hImpossible

/-- Abstract meta-theory interface for Constructor Theory over a fixed
nucleus `R`. Concrete substrates (Surreal, CA, quantum, …) are expected to
provide instances of this class. -/
class Meta (R : Nucleus α) where

  /-- The syntactic type of networks / wiring diagrams of tasks. -/
  Network : Type v

  /-- Multiset of component task-expressions used in a network. -/
  components : Network → Multiset α

  /-- Semantics of a network as a single task-expression in the ambient
  lattice. -/
  denote : Network → α

  /-- Well-formedness / no-bad-wiring predicate on networks. -/
  regular : Network → Prop

  /-- Composition Principle: a regular network whose components are each
  globally possible (for the nucleus `R`) has a globally possible overall
  semantics. -/
  composition_principle :
    ∀ N, regular N →
      (∀ a : α, a ∈ components N → possible R a) →
      possible R (denote N)

  /-- Predicate marking information variables among ambient task-expressions. -/
  isInfoVariable : α → Prop

  /-- Interoperability: combining two information variables yields another
  information variable whose joint task-expression remains possible. Here we
  use `⊓` as the generic way of combining variables; concrete instances may
  interpret this as meet, product, or another joint construction. -/
  interoperability :
    ∀ {x y : α}, isInfoVariable x → isInfoVariable y →
      isInfoVariable (x ⊓ y) ∧ possible R (x ⊓ y)

  /-- Locality principle expressed as a factorization constraint on `R`: if
  a composite `a ⊓ b` is `R`-stable, then `R`-stabilised “parts” exist that
  reconstruct the composite. The precise formulation is substrate-dependent;
  this field records the existence of such a factorisation. -/
  locality :
    ∀ {a b : α}, R (a ⊓ b) = a ⊓ b →
      ∃ a' b',
        R a = a' ∧
        R b = b' ∧
        a' ⊓ b' = a ⊓ b

  /-- Occam operator on task-expressions. Concrete instances are expected
  to relate this to birth-index or Ωᵣ-based minimality. -/
  Occam : α → α

  /-- Principle of Sufficient Reason as a tag on ambient task-expressions.
  Detailed laws connecting this to fixed points of `R` live in substrate
  adapter modules. -/
  PSR : α → Prop

  /-- Dialectic synthesis operator on task-expressions. Instances connect
  this to concrete constructions (e.g. closure of joins) in a substrate. -/
  Dialectic : α → α → α

end Constructor
end HeytingLean
