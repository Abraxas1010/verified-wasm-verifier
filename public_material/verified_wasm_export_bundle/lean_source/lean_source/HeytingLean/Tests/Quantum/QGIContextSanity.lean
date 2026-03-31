import HeytingLean.Quantum.QGIContext
import HeytingLean.Quantum.QGIModel

/-
Compile-only sanity checks for the QGI composite context:

* availability of the QGI interior nucleus and QLMap,
* basic wiring between the QGI substrate and these structures.

We deliberately do not attempt to construct a full `VacuumOmegaRContext`
instance here, as that requires choosing a concrete `LoF.Reentry` model
compatible with the strengthened axioms.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.QGIContext
open HeytingLean.Quantum.QGIModel

-- Check that the QGI interior nucleus and QLMap definitions are available.
#check qgiInterior
#check qgiQLMap

-- Check that the basic QGI amplitude / phase API is still intact.
noncomputable def exampleProfile : PhaseProfile :=
  { φ_lab := fun T => T
    φ_free := fun T => 2 * T }

#check amp
#check interferencePhase

-- Check that the concrete QGI Ωᴿ context is available and carries the
-- vacuum ↔ Euler-boundary equivalence.
#check qgiBaseContext
#check qgiBaseContext.vacuumOmega_eq_eulerBoundary
#check QGIContext.default.base.vacuumOmega_eq_eulerBoundary

end HeytingLean.Tests.Quantum
