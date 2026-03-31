import Mathlib.Data.Real.Basic

/-!
# Correlation scaffolding for Darwin's Cage

This file defines the lightweight numeric structures used across the Darwin's Cage
modules: samples linking human variables to AI features, correlation/performance
thresholds, and helper predicates for interpreting Francisco's metrics.
-/

namespace HeytingLean
namespace DarwinsCage

/-- Which correlation / dependence metric a sample represents. -/
inductive CorrelationKind
  | pearson
  | spearman
  | kendall
  | mutualInfo
  | cosine
  deriving DecidableEq, Repr

/-- Triple capturing a correlation measurement between a human variable and an AI feature. -/
structure CorrelationSample (L : Type*) where
  human : L
  feature : L
  kind : CorrelationKind := .pearson
  value : ℝ

/-- Default correlation bounds taken from Francisco's experiments. -/
structure CorrelationBounds where
  /-- Threshold above which the AI is considered cage-locked. -/
  locked : ℝ := (7 : ℝ) / 10
  /-- Lower bound for the transition band. -/
  transition : ℝ := (1 : ℝ) / 2
  deriving Inhabited

/-- A helper predicate indicating that a numeric correlation meets the "locked" criterion. -/
def highCorrelation (value : ℝ) (bounds : CorrelationBounds := {}) : Prop :=
  value ≥ bounds.locked

/-- A predicate describing correlations that land inside the transition band. -/
def transitionCorrelation (value : ℝ) (bounds : CorrelationBounds := {}) : Prop :=
  bounds.transition ≤ value ∧ value < bounds.locked

/-- Snapshot of performance metrics (max correlation + R²). -/
structure PerformanceSnapshot where
  maxCorr : ℝ
  rSquared : ℝ
  deriving Inhabited

/-- Convenience predicate for R² checks with configurable threshold. -/
def meetsPerformance (perf : PerformanceSnapshot) (threshold : ℝ) : Prop :=
  perf.rSquared ≥ threshold

end DarwinsCage
end HeytingLean
