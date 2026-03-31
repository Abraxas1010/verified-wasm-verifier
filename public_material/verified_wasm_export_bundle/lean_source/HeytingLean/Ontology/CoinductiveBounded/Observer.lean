import HeytingLean.Ontology.CoinductiveBounded.Bounded
import HeytingLean.Genesis.Observer
import HeytingLean.Genesis.CantorWitness
import HeytingLean.PerspectivalPlenum.SheafLensCategory

/-!
# Ontology.CoinductiveBounded.Observer

An ontology observer refines a bounded observation with finite Cantor-prefix
phase-selection data. The ontology layer's pre-existing `BoundedObservation`
is the observer's output surface after forgetting the choice-path component.

This file stays conservative:

- the observer core is generic over carrier and observation types,
- graph-side constructors reuse the existing bounded graph observation, and
- the first plenum bridge is a concrete witness-presheaf section, not a full
  equivalence theorem with the entire sheaf semantics.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

open HeytingLean.Genesis
open HeytingLean.PerspectivalPlenum

universe u v

/-- Finite prefix of a Cantor-space path. -/
abbrev ChoicePath (depth : Nat) : Type :=
  Fin depth → Bool

/-- A bounded observer stabilizes when two successive observation depths agree on the carrier. -/
def StabilizesAt {C : Type u} {Obs : Type v}
    (contexts : Nat → ObservationContext C Obs) (carrier : C) (depth : Nat) : Prop :=
  (contexts depth).observe carrier = (contexts (depth + 1)).observe carrier

/--
An ontology observer remembers a bounded depth, a finite Cantor-prefix of choices,
an observation family indexed by unrolling depth, and a stabilization witness for
the chosen carrier at the declared depth.
-/
structure Observer (C : Type u) (Obs : Type v) where
  depth : Nat
  choices : ChoicePath depth
  contexts : Nat → ObservationContext C Obs
  carrier : C
  stabilizes : StabilizesAt contexts carrier depth

namespace Observer

variable {C : Type u} {Obs : Type v}

/-- Forget the phase path and recover the observer's bounded output surface. -/
def toBoundedObservation (obs : Observer C Obs) : BoundedObservation C Obs where
  depth := obs.depth
  observe := (obs.contexts obs.depth).observe
  respects_bisim := (obs.contexts obs.depth).respects_bisim

@[simp] theorem toBoundedObservation_depth (obs : Observer C Obs) :
    obs.toBoundedObservation.depth = obs.depth :=
  rfl

@[simp] theorem toBoundedObservation_observe (obs : Observer C Obs) :
    obs.toBoundedObservation.observe obs.carrier = (obs.contexts obs.depth).observe obs.carrier :=
  rfl

/-- The stabilization witness survives after forgetting the observer's choice path. -/
theorem stabilization_on_erased_image (obs : Observer C Obs) :
    obs.toBoundedObservation.observe obs.carrier =
      (obs.contexts (obs.depth + 1)).observe obs.carrier :=
  obs.stabilizes

/-- Canonical completion of the finite Cantor prefix to an infinite path. -/
def completedChoices (obs : Observer C Obs) : CompletedObserver :=
  fun n => if h : n < obs.depth then obs.choices ⟨n, h⟩ else false

@[simp] theorem completedChoices_agrees (obs : Observer C Obs) (i : Fin obs.depth) :
    obs.completedChoices i = obs.choices i := by
  simp [completedChoices, i.is_lt]

/--
Any bounded observation can be seen as an observer image by taking a constant
observation family and adding finite path data.
-/
def ofBoundedObservation (B : BoundedObservation C Obs)
    (carrier : C) (choices : ChoicePath B.depth) : Observer C Obs where
  depth := B.depth
  choices := choices
  contexts := fun _ =>
    { observe := B.observe
      respects_bisim := B.respects_bisim }
  carrier := carrier
  stabilizes := rfl

@[simp] theorem toBoundedObservation_ofBoundedObservation
    (B : BoundedObservation C Obs) (carrier : C) (choices : ChoicePath B.depth) :
    (ofBoundedObservation B carrier choices).toBoundedObservation = B := by
  cases B
  rfl

end Observer

/-- Graph-side observation contexts reused by graph observers. -/
noncomputable def graphObservationContext (depth : Nat) :
    ObservationContext GraphCarrier GraphSignal where
  observe := boundedObserveGraph depth
  respects_bisim := True

/-- Graph-backed observer using the existing bounded graph observation family. -/
noncomputable def graphObserver (G : GraphCarrier) (depth : Nat) (choices : ChoicePath depth)
    (hstab : boundedObserveGraph depth G = boundedObserveGraph (depth + 1) G) :
    Observer GraphCarrier GraphSignal where
  depth := depth
  choices := choices
  contexts := graphObservationContext
  carrier := G
  stabilizes := hstab

@[simp] theorem graphObserver_forget_eq (G : GraphCarrier) (depth : Nat) (choices : ChoicePath depth)
    (hstab : boundedObserveGraph depth G = boundedObserveGraph (depth + 1) G) :
    (graphObserver G depth choices hstab).toBoundedObservation = graphBoundedObservation depth :=
  rfl

/-- A strict lens that witnesses exactly the carrier selected by an observer. -/
def observerLens (obs : Observer GraphCarrier GraphSignal) :
    Lens.SemanticLens GraphCarrier where
  profile :=
    { name := "coinductive-observer"
      contradictionPolicy := Lens.ContradictionPolicy.constructive
      dimension := obs.depth
      languageTag := "coinductive-bounded"
      metricTag := "choice-path" }
  witness := fun G => G = obs.carrier
  contradicts := fun _ => False

/-- Lens object induced by an ontology observer. -/
def observerLensObj (obs : Observer GraphCarrier GraphSignal) :
    LensSheaf.LensObj GraphCarrier :=
  ⟨observerLens obs⟩

/-- An ontology observer determines a local witness section in the plenum witness presheaf. -/
def observerWitnessSection (obs : Observer GraphCarrier GraphSignal) :
    LensSheaf.WitnessSection (observerLensObj obs) :=
  ⟨obs.carrier, rfl⟩

@[simp] theorem observerWitnessSection_val (obs : Observer GraphCarrier GraphSignal) :
    (observerWitnessSection obs).1 = obs.carrier :=
  rfl

theorem observer_is_local_section (obs : Observer GraphCarrier GraphSignal) :
    LensSheaf.ExistsInPlenum obs.carrier := by
  exact LensSheaf.existsInPlenum_of_localWitness (observerLensObj obs) (observerWitnessSection obs).2

end HeytingLean.Ontology.CoinductiveBounded
