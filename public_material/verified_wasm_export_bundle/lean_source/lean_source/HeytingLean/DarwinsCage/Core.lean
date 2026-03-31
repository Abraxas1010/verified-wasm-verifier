import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Nucleus
import HeytingLean.DarwinsCage.CageStatus
import HeytingLean.DarwinsCage.Representation

/-!
# Core Darwin's Cage reasoning helpers

This module provides the Heyting-algebra-specific operations (classical collapse,
pre-classical predicate) and bookkeeping structures connecting performance,
correlation, and nucleus membership. No heavy theorems are proven here — the goal
is to capture the data needed for later proofs.
-/

namespace HeytingLean
namespace DarwinsCage

open scoped Classical

/-- Collapse a Heyting element into the Boolean shadow by forcing excluded middle. -/
def classicalCollapse {L : Type*} [HeytingAlgebra L] (x : L) : L :=
  x ⊔ xᶜ

/-- A point is pre-classical when the collapse strictly changes it. -/
def preClassical {L : Type*} [HeytingAlgebra L] (x : L) : Prop :=
  classicalCollapse x ≠ x

/-- Predicate summarizing the hypotheses we will need to prove cage-breaking later. -/
structure CageBreakingCertificate {L : Type*} [CompleteLattice L] [HeytingAlgebra L]
    (R : Nucleus L) (rep : PhysicsRepresentation L)
    (thresholds : CageThresholds) where
  /-- R² clears Francisco's threshold. -/
  performance_ok :
    rep.performance.rSquared ≥ thresholds.performance
  /-- Representation sits in the pre-classical region. -/
  pre_classical : preClassical rep.raw
  /-- Raw representation is already stabilized by the nucleus. -/
  raw_fixed : R rep.raw = rep.raw
  /-- AI-discovered features live in the nucleus core. -/
  feature_fixed : ∀ f ∈ rep.aiFeatures, R f = f
  /-- No human/feature pair has a locked-level correlation. -/
  correlation_gap :
    allLowCorrelation rep thresholds.toCorrelationBounds

/-- A certificate immediately witnesses `cageBroken`. -/
def CageBreakingCertificate.toCageBroken {L : Type*} [CompleteLattice L] [HeytingAlgebra L]
    {R : Nucleus L} {rep : PhysicsRepresentation L}
    {thresholds : CageThresholds}
    (cert : CageBreakingCertificate R rep thresholds) :
    cageBroken R rep thresholds.toCorrelationBounds :=
  ⟨cert.correlation_gap, cert.raw_fixed, cert.feature_fixed⟩

end DarwinsCage
end HeytingLean
