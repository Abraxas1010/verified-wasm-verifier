import HeytingLean.Ontology.CoinductiveBounded.Stabilized

/-!
# Ontology.CoinductiveBounded.BackendIndependence

The first backend-independence theorem package for the coinductive bounded
ontology.

This module is intentionally modest. It does not claim that every ontology-level
construction is now substrate-independent. It proves the first honest transport
theorem on the existing implemented surface:

- if two backend-tagged behaviors have the same interpreted support at the same
  bounded depth, their stabilized meanings agree, and
- the ontology's core-nucleus route agrees with the certified direct route on
  that shared support.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

open HeytingLean.Genesis

/-- Backend-neutral behavioral summary used by the first transport theorem. -/
structure SupportBehavior where
  backend : CarrierBackend
  depth : Nat
  support : Support

/-- Graph behavior interpreted through the ontology support carrier. -/
noncomputable def graphBehavior (depth : Nat) (G : GraphCarrier) : SupportBehavior where
  backend := .graph
  depth := depth
  support := graphSignalSupport (boundedObserveGraph depth G)

/-- Coalgebra behavior interpreted through the ontology support carrier. -/
def coalgebraBehavior (depth : Nat)
    (s : CoalgebraExamples.bitFlipDFA.V) (w : List Bool) : SupportBehavior where
  backend := .coalgebra
  depth := depth
  support := boolSupport ((CoalgebraExamples.wordObservation depth).observe s w)

/--
Behavioral equivalence for the current ontology slice: different backends, the
same bounded depth, and the same interpreted support.
-/
structure ObservationBehaviorEquiv (b₁ b₂ : SupportBehavior) : Prop where
  differentBackend : b₁.backend ≠ b₂.backend
  sameDepth : b₁.depth = b₂.depth
  sameSupport : b₁.support = b₂.support

/-- Direct closure route on interpreted support through the core nucleus. -/
def coreSupportRoute (b : SupportBehavior) : StabilizedMeaning Support :=
  StabilizedMeaning.close supportCoreNucleus b.support

/-- Direct closure route on interpreted support through the certified nucleus. -/
def certifiedSupportRoute (b : SupportBehavior) :
    HeytingLean.Nucleus.CertifiedFixedPoint supportCertifiedNucleus :=
  certifyFixedPoint supportCertifiedNucleus b.support

@[simp] theorem graphBehavior_coreSupportRoute (depth : Nat) (G : GraphCarrier) :
    coreSupportRoute (graphBehavior depth G) =
      fromGraphToStabilized (boundedObserveGraph depth G) :=
  rfl

@[simp] theorem coalgebraBehavior_coreSupportRoute (depth : Nat)
    (s : CoalgebraExamples.bitFlipDFA.V) (w : List Bool) :
    coreSupportRoute (coalgebraBehavior depth s w) =
      fromCoalgebraToStabilized depth s w :=
  rfl

@[simp] theorem graphBehavior_certifiedSupportRoute (depth : Nat) (G : GraphCarrier) :
    certifiedSupportRoute (graphBehavior depth G) =
      certifyGraphSignal (boundedObserveGraph depth G) :=
  rfl

@[simp] theorem coalgebraBehavior_certifiedSupportRoute (depth : Nat)
    (s : CoalgebraExamples.bitFlipDFA.V) (w : List Bool) :
    certifiedSupportRoute (coalgebraBehavior depth s w) =
      certifyCoalgebraWord depth s w :=
  rfl

/-- The core and certified nuclei compute the same closure on support. -/
theorem supportCore_eq_certified_apply (S : Support) :
    supportCoreNucleus.R S = supportCertifiedNucleus S := by
  ext x
  simp [supportCoreNucleus, supportCertifiedNucleus]

/--
The ontology's core-nucleus stabilized route and the certified direct route
extract the same support witness.
-/
theorem core_vs_certified_support_route (b : SupportBehavior) :
    (coreSupportRoute b).witness =
      HeytingLean.Nucleus.CertifiedFixedPoint.extract (certifiedSupportRoute b) := by
  simpa [coreSupportRoute, certifiedSupportRoute, certifyFixedPoint,
    StabilizedMeaning.close, HeytingLean.Nucleus.CertifiedFixedPoint.extract,
    HeytingLean.Nucleus.close] using supportCore_eq_certified_apply b.support

/--
If two backend-tagged behaviors have the same interpreted support at the same
bounded depth, the ontology's stabilized meaning agrees across them.
-/
theorem stabilizedMeaning_transport_core {b₁ b₂ : SupportBehavior}
    (h : ObservationBehaviorEquiv b₁ b₂) :
    (coreSupportRoute b₁).witness = (coreSupportRoute b₂).witness := by
  simp [coreSupportRoute, StabilizedMeaning.close, h.sameSupport]

/--
The same behavioral equivalence transports through the certified direct route.
-/
theorem stabilizedMeaning_transport_certified {b₁ b₂ : SupportBehavior}
    (h : ObservationBehaviorEquiv b₁ b₂) :
    HeytingLean.Nucleus.CertifiedFixedPoint.extract (certifiedSupportRoute b₁) =
      HeytingLean.Nucleus.CertifiedFixedPoint.extract (certifiedSupportRoute b₂) := by
  simp [certifiedSupportRoute, certifyFixedPoint,
    HeytingLean.Nucleus.CertifiedFixedPoint.extract, h.sameSupport]

/-- Graph-specialized agreement between the core and certified routes. -/
theorem graphRoute_core_vs_certified (depth : Nat) (G : GraphCarrier) :
    (fromGraphToStabilized (boundedObserveGraph depth G)).witness =
      HeytingLean.Nucleus.CertifiedFixedPoint.extract
        (certifyGraphSignal (boundedObserveGraph depth G)) := by
  simpa using core_vs_certified_support_route (graphBehavior depth G)

/-- Coalgebra-specialized agreement between the core and certified routes. -/
theorem coalgebraRoute_core_vs_certified (depth : Nat)
    (s : CoalgebraExamples.bitFlipDFA.V) (w : List Bool) :
    (fromCoalgebraToStabilized depth s w).witness =
      HeytingLean.Nucleus.CertifiedFixedPoint.extract
        (certifyCoalgebraWord depth s w) := by
  simpa using core_vs_certified_support_route (coalgebraBehavior depth s w)

/-- Worked graph-side behavior used by the first cross-backend example. -/
noncomputable def lifeDepthOneBehavior : SupportBehavior :=
  graphBehavior 1 CoGame.Life

/-- Worked coalgebra-side behavior used by the first cross-backend example. -/
def bitFlipDepthOneBehavior : SupportBehavior :=
  coalgebraBehavior 1 false [true]

@[simp] theorem lifeDepthOne_support :
    lifeDepthOneBehavior.support = ({0} : Set Nat) := by
  simp [lifeDepthOneBehavior, graphBehavior, graphSignalSupport,
    boundedObserveGraph, oscillationExpr, exprSupport, interpretUnroll, CoGame.Life]

@[simp] theorem bitFlipDepthOne_support :
    bitFlipDepthOneBehavior.support = ({0} : Set Nat) := by
  change boolSupport ((CoalgebraExamples.wordObservation 1).observe false [true]) = ({0} : Set Nat)
  rw [CoalgebraExamples.wordObservation_false_true []]
  simp [boolSupport]

/--
First concrete backend-independence witness: the graph `Life` carrier at depth
`1` and the coalgebraic bit-flip witness on `[true]` have the same interpreted
support at the same bounded depth.
-/
theorem life_vs_bitFlip_behavior_equiv :
    ObservationBehaviorEquiv lifeDepthOneBehavior bitFlipDepthOneBehavior := by
  refine ⟨?_, rfl, ?_⟩
  · intro h
    cases h
  · rw [lifeDepthOne_support, bitFlipDepthOne_support]

/--
Worked example: cross-backend behavioral equivalence transports the ontology's
stabilized meaning between the graph and coalgebra routes.
-/
theorem life_vs_bitFlip_stabilized_meaning_example :
    (fromGraphToStabilized (boundedObserveGraph 1 CoGame.Life)).witness =
      (fromCoalgebraToStabilized 1 false [true]).witness := by
  simpa [lifeDepthOneBehavior, bitFlipDepthOneBehavior] using
    stabilizedMeaning_transport_core life_vs_bitFlip_behavior_equiv

/--
Worked example: the same cross-backend behavior also agrees through the direct
certified route.
-/
theorem life_vs_bitFlip_certified_example :
    HeytingLean.Nucleus.CertifiedFixedPoint.extract
        (certifyGraphSignal (boundedObserveGraph 1 CoGame.Life)) =
      HeytingLean.Nucleus.CertifiedFixedPoint.extract
        (certifyCoalgebraWord 1 false [true]) := by
  simpa [lifeDepthOneBehavior, bitFlipDepthOneBehavior] using
    stabilizedMeaning_transport_certified life_vs_bitFlip_behavior_equiv

end HeytingLean.Ontology.CoinductiveBounded
