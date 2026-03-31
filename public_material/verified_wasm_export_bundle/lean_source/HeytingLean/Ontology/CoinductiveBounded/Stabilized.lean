import HeytingLean.Ontology.CoinductiveBounded.Bounded
import Mathlib.Order.Nucleus

/-!
# Ontology.CoinductiveBounded.Stabilized

Bridge bounded observations into the repo's existing nucleus and fixed-point surfaces.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

open HeytingLean.Genesis

/-- Reuse the Genesis support carrier for stabilized bounded meanings. -/
abbrev Support :=
  Genesis.Support

/-- Core-nucleus closure used by the ontology bridge: add the distinguished boundary witness `0`. -/
def supportCoreNucleus : HeytingLean.Core.Nucleus Support where
  R := fun S => S ∪ ({0} : Set Nat)
  extensive := by
    intro S x hx
    exact Or.inl hx
  idempotent := by
    intro S
    ext x
    simp
  meet_preserving := by
    intro A B
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨Or.inl hx.1, Or.inl hx.2⟩
      · exact ⟨Or.inr hx, Or.inr hx⟩
    · intro hx
      rcases hx with ⟨hxA, hxB⟩
      rcases hxA with hxA | hxA
      · rcases hxB with hxB | hxB
        · exact Or.inl ⟨hxA, hxB⟩
        · exact Or.inr hxB
      · exact Or.inr hxA

/-- The same closure exposed through the Mathlib/Certified nucleus helper API. -/
def supportCertifiedNucleus : HeytingLean.Nucleus.CertifiedNucleus Support where
  toInfHom :=
    { toFun := fun S => S ∪ ({0} : Set Nat)
      map_inf' := by
        intro A B
        ext x
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact ⟨Or.inl hx.1, Or.inl hx.2⟩
          · exact ⟨Or.inr hx, Or.inr hx⟩
        · intro hx
          rcases hx with ⟨hxA, hxB⟩
          rcases hxA with hxA | hxA
          · rcases hxB with hxB | hxB
            · exact Or.inl ⟨hxA, hxB⟩
            · exact Or.inr hxB
          · exact Or.inr hxA }
  idempotent' := by
    intro S
    intro x hx
    simp at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  le_apply' := by
    intro S x hx
    exact Or.inl hx

/-- Convert a Boolean observation to the ontology support carrier. -/
def boolSupport (b : Bool) : Support :=
  if b then ({0} : Set Nat) else ∅

/-- Graph path into stabilized meaning. -/
def fromGraphToStabilized (sig : GraphSignal) : StabilizedMeaning Support :=
  StabilizedMeaning.close supportCoreNucleus (graphSignalSupport sig)

/-- Coalgebra path into stabilized meaning, instantiated with the ontology DFA witness. -/
def fromCoalgebraToStabilized (depth : Nat)
    (s : CoalgebraExamples.bitFlipDFA.V) (w : List Bool) : StabilizedMeaning Support :=
  StabilizedMeaning.close supportCoreNucleus
    (boolSupport ((CoalgebraExamples.wordObservation depth).observe s w))

theorem fromGraphToStabilized_fixed (sig : GraphSignal) :
    (fromGraphToStabilized sig).witness ∈ supportCoreNucleus.fixedPoints :=
  StabilizedMeaning.witness_mem_fixedPoints (fromGraphToStabilized sig)

theorem fromCoalgebraToStabilized_fixed (depth : Nat)
    (s : CoalgebraExamples.bitFlipDFA.V) (w : List Bool) :
    (fromCoalgebraToStabilized depth s w).witness ∈ supportCoreNucleus.fixedPoints :=
  StabilizedMeaning.witness_mem_fixedPoints (fromCoalgebraToStabilized depth s w)

/-- Certified fixed-point witness for graph signals. -/
def certifyGraphSignal (sig : GraphSignal) :
    HeytingLean.Nucleus.CertifiedFixedPoint supportCertifiedNucleus :=
  certifyFixedPoint supportCertifiedNucleus (graphSignalSupport sig)

/-- Certified fixed-point witness for the coalgebraic Boolean observation path. -/
def certifyCoalgebraWord (depth : Nat)
    (s : CoalgebraExamples.bitFlipDFA.V) (w : List Bool) :
    HeytingLean.Nucleus.CertifiedFixedPoint supportCertifiedNucleus :=
  certifyFixedPoint supportCertifiedNucleus
    (boolSupport ((CoalgebraExamples.wordObservation depth).observe s w))

@[simp] theorem boolSupport_true : boolSupport true = ({0} : Set Nat) := by
  simp [boolSupport]

@[simp] theorem boolSupport_false : boolSupport false = (∅ : Set Nat) := by
  simp [boolSupport]

@[simp] theorem fromGraphToStabilized_life_zero :
    (fromGraphToStabilized (boundedObserveGraph 0 CoGame.Life)).witness = ({0} : Set Nat) := by
  ext x
  simp [fromGraphToStabilized, StabilizedMeaning.close, graphSignalSupport,
    boundedObserveGraph, oscillationExpr, supportCoreNucleus, exprSupport,
    interpretUnroll, CoGame.Life]

@[simp] theorem fromCoalgebraToStabilized_false_true_zero :
    (fromCoalgebraToStabilized 1 false [true]).witness = ({0} : Set Nat) := by
  ext x
  simp [fromCoalgebraToStabilized, StabilizedMeaning.close, boolSupport, supportCoreNucleus,
    CoalgebraExamples.wordObservation, CoalgebraExamples.bitFlipDFA,
    HeytingLean.Coalgebra.Universal.Examples.DFA.lang]

end HeytingLean.Ontology.CoinductiveBounded
