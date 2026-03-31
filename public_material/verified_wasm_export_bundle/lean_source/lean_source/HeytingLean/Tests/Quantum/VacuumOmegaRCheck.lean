import HeytingLean.Quantum.VacuumOmegaR

/-
Compile-only sanity for the vacuum ↔ Ωᴿ Euler boundary bridge.

This module does not instantiate a concrete `VacuumOmegaRContext`; it
simply checks that the key theorems are available and inspects their
dependency footprint, as suggested by the blueprint. This avoids introducing
additional dependencies or fixing unrelated test code.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum

-- The main equivalence between the Ωᵣ-level vacuum and the Euler boundary.
#check VacuumOmegaRContext.vacuumOmega_eq_eulerBoundary
#print axioms VacuumOmegaRContext.vacuumOmega_eq_eulerBoundary

-- PSR view: vacuum as a sufficient reason (fixed point of the nucleus).
#check VacuumOmegaRContext.vacuumOmega_psr
#print axioms VacuumOmegaRContext.vacuumOmega_psr

-- Occam / recursive-zero view: vacuum has birthday zero.
#check VacuumOmegaRContext.vacuumOmega_birth_zero
#print axioms VacuumOmegaRContext.vacuumOmega_birth_zero

end HeytingLean.Tests.Quantum
