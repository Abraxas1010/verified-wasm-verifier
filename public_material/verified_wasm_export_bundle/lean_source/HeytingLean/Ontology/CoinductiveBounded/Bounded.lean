import HeytingLean.Ontology.CoinductiveBounded.Carriers
import HeytingLean.Genesis.VirtualUntying
import HeytingLean.Genesis.VirtualCoinductiveSemantics
import HeytingLean.Coalgebra.Universal.Examples.Automata

/-!
# Ontology.CoinductiveBounded.Bounded

Bounded executable observations for the two carrier backends used by the ontology layer.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

open HeytingLean.Genesis
open HeytingLean.Coalgebra.Universal

universe u

/-- The graph-side bounded signal remembers both the head oscillation and the truncated view. -/
abbrev GraphSignal :=
  LoFExpr0 × LoFExpr0

/-- Graph-backed bounded observation: head oscillation plus depth-truncated approximation. -/
noncomputable def boundedObserveGraph (n : Nat) (G : GraphCarrier) : GraphSignal :=
  (oscillationExpr G, interpretUnroll n (unroll n G : SetTheory.PGame.{0}))

/-- Pack the graph bounded observation as a backend-neutral bounded observation. -/
noncomputable def graphBoundedObservation (n : Nat) : BoundedObservation GraphCarrier GraphSignal where
  depth := n
  observe := boundedObserveGraph n
  respects_bisim := True

@[simp] theorem boundedObserveGraph_fst (n : Nat) (G : GraphCarrier) :
    (boundedObserveGraph n G).1 = oscillationExpr G :=
  rfl

@[simp] theorem boundedObserveGraph_snd (n : Nat) (G : GraphCarrier) :
    (boundedObserveGraph n G).2 = interpretUnroll n (unroll n G : SetTheory.PGame.{0}) := by
  simp [boundedObserveGraph]

/-- The bounded graph signal is definitionally aligned with the existing unroll pipeline. -/
theorem graph_projection_respects_existing_unroll (n : Nat) (G : GraphCarrier) :
    (boundedObserveGraph n G).2 =
      virtualInterpretUnroll n (virtualUnroll n G : SetTheory.PGame.{0}) :=
by
  rw [boundedObserveGraph_snd]
  unfold virtualInterpretUnroll virtualUnroll
  rfl

/-- Convert a graph signal to the existing support carrier used by Genesis stabilization. -/
def graphSignalSupport (sig : GraphSignal) : Support :=
  exprSupport sig.1 ∪ exprSupport sig.2

@[simp] theorem graphSignalSupport_mk (a b : LoFExpr0) :
    graphSignalSupport (a, b) = exprSupport a ∪ exprSupport b :=
  rfl

/-- The cycle special case and `Life` agree under the bounded graph observation. -/
theorem cycle_special_case_observation_eq_life (n : Nat) :
    boundedObserveGraph n (cycleCoGame 0) = boundedObserveGraph n CoGame.Life := by
  ext
  · simp [boundedObserveGraph, oscillationExpr, CoGame.Life, cycleCoGame, succOnFin]
  · simp [boundedObserveGraph, interpretUnroll_eq_nesting]

/-- The graph-side bounded observation does not lose the established cycle witness. -/
theorem bounded_projection_preserves_cycle_witness (n : Nat) :
    CoGame.Bisim (cycleCoGame 0) CoGame.Life ∧
      boundedObserveGraph n (cycleCoGame 0) = boundedObserveGraph n CoGame.Life := by
  exact ⟨life_as_cycle_special_case, cycle_special_case_observation_eq_life n⟩

namespace CoalgebraExamples

/-- A concrete two-state DFA coalgebra used as the ontology's non-Genesis witness family. -/
def bitFlipDFA : HeytingLean.Coalgebra.Universal.Examples.DFA (A := Bool) where
  V := Bool
  str := fun s => (s, fun a => if a then !s else s)

/-- Package the DFA as a carrier witness through the universal-coalgebra adapter. -/
def bitFlipWitness : CarrierWitness :=
  fromCoalgebra bitFlipDFA

/-- Bounded automaton observation: evaluate only the prefix of length `depth`. -/
def wordObservation (depth : Nat) :
    BoundedObservation bitFlipDFA.V (List Bool → Bool) where
  depth := depth
  observe := fun s w => HeytingLean.Coalgebra.Universal.Examples.DFA.lang bitFlipDFA s (w.take depth)
  respects_bisim := True

@[simp] theorem wordObservation_apply (depth : Nat) (s : bitFlipDFA.V) (w : List Bool) :
    (wordObservation depth).observe s w =
      HeytingLean.Coalgebra.Universal.Examples.DFA.lang bitFlipDFA s (w.take depth) :=
  rfl

@[simp] theorem wordObservation_depth_zero (s : bitFlipDFA.V) (w : List Bool) :
    (wordObservation 0).observe s w = s := by
  simp [wordObservation, HeytingLean.Coalgebra.Universal.Examples.DFA.lang,
    HeytingLean.Coalgebra.Universal.Examples.DFA.out, bitFlipDFA]

@[simp] theorem wordObservation_false_true (w : List Bool) :
    (wordObservation 1).observe false (true :: w) = true := by
  simp [wordObservation, HeytingLean.Coalgebra.Universal.Examples.DFA.lang,
    HeytingLean.Coalgebra.Universal.Examples.DFA.step,
    HeytingLean.Coalgebra.Universal.Examples.DFA.out, bitFlipDFA]

@[simp] theorem wordObservation_true_false (w : List Bool) :
    (wordObservation 1).observe true (false :: w) = true := by
  simp [wordObservation, HeytingLean.Coalgebra.Universal.Examples.DFA.lang,
    HeytingLean.Coalgebra.Universal.Examples.DFA.step,
    HeytingLean.Coalgebra.Universal.Examples.DFA.out, bitFlipDFA]

end CoalgebraExamples

end HeytingLean.Ontology.CoinductiveBounded
