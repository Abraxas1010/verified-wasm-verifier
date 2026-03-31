import HeytingLean.Quantum.VacuumOmegaRBridge

/-
Compile-only sanity checks for the high-level Vacuum–Ωᴿ + phase/gravity bridge.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.VacuumOmegaRBridge

-- Check the QGI-style phase model and integrated bridge structures.
#check QGIPhaseModel
#check VacuumGravityBridge
#check mkDefaultBridge

end HeytingLean.Tests.Quantum

