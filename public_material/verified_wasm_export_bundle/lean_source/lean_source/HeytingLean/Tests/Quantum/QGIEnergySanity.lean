import HeytingLean.Quantum.EnergyObservable
import HeytingLean.Quantum.QGIEnergyObservable
import HeytingLean.Quantum.QGIContext

/-!
Compile-only sanity checks for the QGI energy observable in the finite
example model.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.QGI
open HeytingLean.Quantum.QGIContext

-- Basic spectral abstractions.
#check EnergyObservable
#check energyDemo

-- Vacuum as a ground state for the finite energy observable.
#check vacuum_is_ground_state
#check vacuum_is_ground_state_energyDemo

-- Bridge to the Euler boundary in Ωᴿ.
#check ground_state_is_euler
#check ground_state_is_euler
  (H := energyDemo)
  (C := qgiBaseContext)
  (hground := vacuum_is_ground_state_energyDemo)

-- Concrete equality in the QGI base context, now viewed spectrally.
example :
    qgiBaseContext.vacuumOmega = qgiBaseContext.R.eulerBoundary :=
  ground_state_is_euler
    (H := energyDemo)
    (C := qgiBaseContext)
    (hground := vacuum_is_ground_state_energyDemo)

end HeytingLean.Tests.Quantum
