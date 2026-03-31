import HeytingLean.Bridge.NoCoincidence.Nucleus.AdviceAsNucleus
import HeytingLean.Core.HeytingAlgebra

namespace HeytingLean.Bridge.NoCoincidence.Meta

open HeytingLean
open HeytingLean.Bridge.NoCoincidence.Nucleus

/-- Nucleus-induced heuristic implication on circuit properties. -/
def heuristicImplication (R : CircuitNucleus n) (evidence claim : CircuitProp n) : CircuitProp n :=
  Core.Nucleus.himp R.toNucleus evidence claim

/-- A heuristic argument is evidence that survives the nucleus-induced implication. -/
def HeuristicArgument (R : CircuitNucleus n) (evidence claim : CircuitProp n) : Prop :=
  ∀ C, evidence C → heuristicImplication R evidence claim C

theorem heuristic_from_entailment (R : CircuitNucleus n) (evidence claim : CircuitProp n)
    (h : ∀ C, evidence C → claim C) :
    HeuristicArgument R evidence claim := by
  intro C hEvidence
  exact R.toNucleus.extensive (fun D => evidence D → claim D) C (h C)

/-- Reflexive heuristic for the property lens: once the evidence is already `PropertyP`, the
induced heuristic implication returns it unchanged. -/
theorem property_lens_reflexive_heuristic (n : ℕ) :
    HeuristicArgument (propertyNucleus n) (propertyFocus n) (propertyFocus n) := by
  apply heuristic_from_entailment
  intro C hC
  exact hC

end HeytingLean.Bridge.NoCoincidence.Meta
