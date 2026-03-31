import HeytingLean.DarwinsCage.Core

/-!
# Quantum scaffolding

Provides the abstractions needed to describe Francisco's quantum (W1, B3, …)
experiments. The definitions below stay agnostic to the exact quantum model; they
only require a nucleus and a representation living in the Heyting image.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Physics

open scoped Classical

variable {L : Type*} [CompleteLattice L]

/-- Helper predicate asserting that every target observable is decorrelated from the AI features. -/
def uncorrelatedWithTargets (rep : PhysicsRepresentation L) (targets : List L)
    (bounds : CorrelationBounds := {}) : Prop :=
  ∀ t ∈ targets, ∀ f ∈ rep.aiFeatures, ¬highCorrelationWith rep t f bounds

/-- If the target list is exactly the `humanVars`, then uncorrelatedness implies
`allLowCorrelation`. -/
theorem allLowCorrelation_of_uncorrelatedWithTargets
    (rep : PhysicsRepresentation L) (targets : List L)
    (bounds : CorrelationBounds := {})
    (h_targets : targets = rep.humanVars) :
    uncorrelatedWithTargets rep targets bounds → allLowCorrelation rep bounds := by
  intro h_uncorr h hh f hf
  have hh' : h ∈ targets := by simpa [h_targets] using hh
  exact h_uncorr h hh' f hf

/-- Scenario bundle for the quantum experiments. -/
structure QuantumScenario (L : Type*) [CompleteLattice L] [HeytingAlgebra L] where
  nucleus : Nucleus L
  rep : PhysicsRepresentation L
  classicalTargets : List L
  targets_eq_humanVars : classicalTargets = rep.humanVars
  learnsQuantumDynamics : Prop
  learnsEvidence : learnsQuantumDynamics
  bounds : CorrelationBounds := {}
  thresholds : CageThresholds := {}
  perf_ok : thresholds.performance ≤ rep.performance.rSquared
  corr_not_locked : ¬thresholds.locked ≤ rep.performance.maxCorr
  corr_low : ¬thresholds.transition ≤ rep.performance.maxCorr
  uncorrelatedTargets : uncorrelatedWithTargets rep classicalTargets bounds
  raw_fixed : nucleus rep.raw = rep.raw
  feature_fixed : ∀ f ∈ rep.aiFeatures, nucleus f = f

/-- Goal condition for the W1/B3 style experiments. -/
def QuantumScenario.cageBreakingGoal {L : Type*} [CompleteLattice L] [HeytingAlgebra L]
    (scenario : QuantumScenario L) : Prop :=
  uncorrelatedWithTargets scenario.rep scenario.classicalTargets scenario.bounds ∧
    scenario.learnsQuantumDynamics ∧
    cageBroken scenario.nucleus scenario.rep scenario.bounds ∧
    determineCageStatus scenario.rep.performance scenario.thresholds = CageStatus.broken

end Physics
end DarwinsCage
end HeytingLean
