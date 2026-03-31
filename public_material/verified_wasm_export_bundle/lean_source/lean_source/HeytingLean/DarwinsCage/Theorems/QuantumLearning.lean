import HeytingLean.DarwinsCage.Physics.Quantum
import HeytingLean.DarwinsCage.Experiments.Exp3Phase
import HeytingLean.DarwinsCage.Experiments.ExpB3Entanglement
import HeytingLean.DarwinsCage.Experiments.ExpW1Quantum
import HeytingLean.DarwinsCage.Tests.CageStatus

/-!
# Quantum learning theorem scaffolding

Because `QuantumScenario` packages the evidence required by its goal predicate,
the experiment goals become immediate lemmas. Later work can replace these
evidence fields with derived proofs from more primitive hypotheses.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Theorems

open Physics Experiments

variable {L : Type*} [CompleteLattice L] [HeytingAlgebra L]

/-- Every `QuantumScenario` satisfies its goal predicate from stored evidence. -/
theorem quantumScenario_goal (scenario : QuantumScenario L) :
    scenario.cageBreakingGoal := by
  have hCorrGap : allLowCorrelation scenario.rep scenario.bounds :=
    Physics.allLowCorrelation_of_uncorrelatedWithTargets
      (rep := scenario.rep)
      (targets := scenario.classicalTargets)
      (bounds := scenario.bounds)
      scenario.targets_eq_humanVars
      scenario.uncorrelatedTargets
  have hBroken : cageBroken scenario.nucleus scenario.rep scenario.bounds :=
    ⟨hCorrGap, scenario.raw_fixed, scenario.feature_fixed⟩
  have hStatus :
      determineCageStatus scenario.rep.performance scenario.thresholds = CageStatus.broken :=
    Tests.classify_broken (t := scenario.thresholds)
      (maxCorr := scenario.rep.performance.maxCorr)
      (rSquared := scenario.rep.performance.rSquared)
      scenario.perf_ok
      scenario.corr_not_locked
      scenario.corr_low
  exact ⟨scenario.uncorrelatedTargets, scenario.learnsEvidence, hBroken, hStatus⟩

theorem exp3_phase_breaks_cage (exp : Exp3Phase L) : exp.goal := by
  dsimp [Exp3Phase.goal]
  exact quantumScenario_goal exp.scenario

theorem expB3_entanglement_breaks_cage (exp : ExpB3Entanglement L) : exp.goal := by
  dsimp [ExpB3Entanglement.goal]
  exact quantumScenario_goal exp.scenario

theorem expW1_quantum_breaks_cage (exp : ExpW1Quantum L) : exp.goal := by
  dsimp [ExpW1Quantum.goal]
  exact quantumScenario_goal exp.scenario

end Theorems
end DarwinsCage
end HeytingLean
