import HeytingLean.DarwinsCage.Representation

/-!
# Darwin's Cage backend interface (Phase 8)

This module defines a minimal, backend-agnostic interface for producing
experiment "traces" from which Darwin's Cage metrics (correlations + performance)
can be extracted.

The first version is intentionally simple and pure: a backend returns a record
already containing the summary statistics and correlation samples. More detailed
time-series models can be layered on later without changing the core API.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Backends

open scoped Classical

variable {L : Type*} [CompleteLattice L]

/-- Minimal experimental trace: a packaged representation snapshot. -/
structure Trace (L : Type*) [CompleteLattice L] where
  raw : L
  humanVars : List L
  aiFeatures : List L
  correlations : List (CorrelationSample L)
  performance : PerformanceSnapshot

/-- Convert a trace into a Darwin's Cage `PhysicsRepresentation`. -/
def Trace.toRepresentation (trace : Trace L) : PhysicsRepresentation L :=
  { raw := trace.raw
    humanVars := trace.humanVars
    aiFeatures := trace.aiFeatures
    correlations := trace.correlations
    performance := trace.performance }

/-- A backend produces a trace from some configuration parameter. -/
structure Backend (L : Type*) [CompleteLattice L] where
  Config : Type
  run : Config → Trace L

end Backends
end DarwinsCage
end HeytingLean

