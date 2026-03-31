import HeytingLean.Quantum.OML.Examples.QGIInterferometer
import HeytingLean.Quantum.QGIModel

/-
Compile-only sanity checks for the QGI substrate:

* orthogonality of the two path propositions,
* basic amplitude/phase API wiring.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.OML
open HeytingLean.Quantum.OML.QGIInterferometer
open HeytingLean.Quantum.QGIModel

/-- Sanity check: the two QGI path propositions are orthogonal. -/
example :
    (labPath ⊓ freePath : QGIβ) = ⊥ :=
  QGIInterferometer.inf_lab_free

/-- A simple example phase profile for compile-time checking. -/
noncomputable def exampleProfile : QGIModel.PhaseProfile where
  φ_lab  := fun T => T
  φ_free := fun T => 2 * T

-- Check the main QGI model API surfaces compile.
#check QGIModel.amp
#check QGIModel.interferencePhase
#check QGIModel.interferencePhase_eq_t3

end HeytingLean.Tests.Quantum
