import HeytingLean.DarwinsCage.Physics.Relativistic
import HeytingLean.DarwinsCage.Experiments.Exp2Relativity
import HeytingLean.DarwinsCage.Tests.CageStatus

/-!
# Geometric learning theorem scaffold

Connects Experiment 2 with the relativistic scenario goal.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Theorems

open Physics Experiments

/-- Experiment 2 satisfies the relativistic cage-breaking goal. -/
theorem exp2_relativistic_breaks_cage (exp : Exp2Relativity) :
    exp.goal := by
  dsimp [Exp2Relativity.goal, RelativisticScenario.cageBreakingGoal]
  have hBroken : cageBroken exp.scenario.R exp.scenario.rep exp.scenario.bounds :=
    ⟨exp.scenario.corr_gap, exp.scenario.raw_fixed, exp.scenario.feature_fixed⟩
  have hStatus :
      determineCageStatus exp.scenario.rep.performance exp.scenario.thresholds = CageStatus.broken :=
    Tests.classify_broken (t := exp.scenario.thresholds)
      (maxCorr := exp.scenario.rep.performance.maxCorr)
      (rSquared := exp.scenario.rep.performance.rSquared)
      exp.scenario.perf_ok
      exp.scenario.corr_not_locked
      exp.scenario.corr_low
  exact ⟨exp.scenario.learnsEvidence, exp.scenario.extrapEvidence, hBroken, hStatus⟩

end Theorems
end DarwinsCage
end HeytingLean
