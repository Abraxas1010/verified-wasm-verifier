import HeytingLean.Physics.SpinGlass.Model
import HeytingLean.Physics.SpinGlass.Phase
import HeytingLean.Physics.SpinGlass.ChaosReentrance
import HeytingLean.Logic.PSR.Robustness

/-
# Chaos & Reentrance contract guards

This module exposes a small set of guard predicates that contract
layers can use to reason about temperature chaos and reentrance in
spin-glass reports.  It is deliberately modest:

* `ChaosDiagnostics` summarises the outcome of an external analysis
  (e.g. the `verify_chaos` executable),
* `RequiresNoReentrance` blocks flows when EA-plane reentrance is
  detected, and
* `ChaosBudget` encodes a simple budgeted policy in the presence of
  temperature chaos and PSR robustness flags.

Higher-level policies should be built on top of these primitives.
-/

namespace HeytingLean
namespace Contracts
namespace ChaosGuards

open HeytingLean.Physics.SpinGlass
open HeytingLean.Logic

/-- Diagnostics summary for the Chaos & Reentrance lens.

These fields are intended to be populated by an executable verifier
(`verify_chaos`) based on empirical reports; the guards below interpret
them as policy constraints. -/
structure ChaosDiagnostics where
  hasReentrance : Bool
  hasTempChaos  : Bool
  psrOk         : Bool
  notes         : String
  deriving Repr

/-- Guard: require that no EA-plane reentrance has been detected. -/
def RequiresNoReentrance (diag : ChaosDiagnostics) : Prop :=
  diag.hasReentrance = false

/-- Guard: allow a controlled budget of temperature chaos.

* If `hasTempChaos = false`, the guard passes trivially.
* If `hasTempChaos = true`, we require `psrOk = true`; any additional
  numeric thresholds (e.g. on Δβ) are handled by the caller and can
  be encoded into `notes` or an extended diagnostics type.
-/
def ChaosBudget (diag : ChaosDiagnostics) : Prop :=
  diag.hasTempChaos = false ∨
    (diag.hasTempChaos = true ∧ diag.psrOk = true)

/-- Bridge from spec-level predicates to diagnostics: construct a
`ChaosDiagnostics` record from reentrance, temperature-chaos, and PSR
flags plus a free-form note. -/
def mkDiagnostics
    (reentrant : Bool) (tempChaos : Bool)
    (psrOk : Bool) (notes : String) : ChaosDiagnostics :=
  { hasReentrance := reentrant
    hasTempChaos  := tempChaos
    psrOk         := psrOk
    notes         := notes }

end ChaosGuards
end Contracts
end HeytingLean

