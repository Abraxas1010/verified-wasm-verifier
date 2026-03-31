import HeytingLean.Core.Nucleus
import HeytingLean.Nucleus.Certified

/-!
# Ontology.CoinductiveBounded.Core

Backend-neutral vocabulary for the coinductive bounded ontology surface.

This module does not choose a concrete carrier encoding. It only fixes the shared
shape of:

- backend tags,
- observation contexts,
- bounded observations, and
- stabilized meanings landing in the existing nucleus infrastructure.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

universe u v

/-- Explicit backend tag: graph witnesses and universal-coalgebra witnesses are both first-class. -/
inductive CarrierBackend
  | graph
  | coalgebra
  deriving DecidableEq, Repr

/-- A context in which a carrier can be observed. -/
structure ObservationContext (C : Type u) (Obs : Type v) where
  observe : C → Obs
  /-- This field is a contract placeholder, not a second bisimulation theory. -/
  respects_bisim : Prop

/-- A bounded observation packages a depth with its observation map. -/
structure BoundedObservation (C : Type u) (Obs : Type v) extends ObservationContext C Obs where
  depth : Nat

/--
Stable meaning is a witness together with the existing `Core.Nucleus` that fixes it.
This keeps the ontology layer on the repo's nucleus surface instead of inventing a new one.
-/
structure StabilizedMeaning (L : Type u) [SemilatticeInf L] [OrderBot L] where
  nucleus : HeytingLean.Core.Nucleus L
  witness : L
  fixed : nucleus.R witness = witness

namespace StabilizedMeaning

variable {L : Type u} [SemilatticeInf L] [OrderBot L]

/-- Every stabilized meaning witnesses membership in the nucleus fixed-point locus. -/
theorem witness_mem_fixedPoints (m : StabilizedMeaning L) :
    m.witness ∈ m.nucleus.fixedPoints := by
  exact m.fixed

/-- Close any element into stabilized meaning using the core nucleus. -/
def close (N : HeytingLean.Core.Nucleus L) (x : L) : StabilizedMeaning L where
  nucleus := N
  witness := N.R x
  fixed := N.idempotent x

@[simp] theorem close_witness (N : HeytingLean.Core.Nucleus L) (x : L) :
    (close N x).witness = N.R x :=
  rfl

end StabilizedMeaning

/-- Re-export the certified fixed-point helper on the Mathlib nucleus side. -/
def certifyFixedPoint {X : Type u} [SemilatticeInf X]
    (n : HeytingLean.Nucleus.CertifiedNucleus X) (x : X) :
    HeytingLean.Nucleus.CertifiedFixedPoint n :=
  HeytingLean.Nucleus.close n x

end HeytingLean.Ontology.CoinductiveBounded
