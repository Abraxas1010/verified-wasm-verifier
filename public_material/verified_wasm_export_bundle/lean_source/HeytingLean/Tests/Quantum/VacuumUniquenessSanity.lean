import HeytingLean.LoF.Nucleus
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.VacuumPhaseUniqueness

/-
Compile-only sanity checks for vacuum / Euler-boundary uniqueness lemmas.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.LoF
open HeytingLean.Quantum

-- Core LoF-level uniqueness of the Euler boundary.
#check Reentry.eulerBoundary_unique_minimal

-- Context-level uniqueness of the Ωᴿ vacuum as minimal fixed point.
#check VacuumOmegaRContext.vacuumOmega_unique_minimal
-- Support-aware variant.
#check VacuumOmegaRContext.vacuumOmega_unique_minimal_support

-- Witness-image construction and uniqueness.
#check VacuumOmegaRContext.witnessImage
#check VacuumOmegaRContext.witnessImage_eq_eulerBoundary
#check VacuumOmegaRContext.vacuum_image_unique

-- Phase / T³-based uniqueness structures and lemma.
#check VacuumPhaseUniqueness.PhaseMassModel
#check VacuumPhaseUniqueness.vacuum_unique_by_zero_phase

end HeytingLean.Tests.Quantum
