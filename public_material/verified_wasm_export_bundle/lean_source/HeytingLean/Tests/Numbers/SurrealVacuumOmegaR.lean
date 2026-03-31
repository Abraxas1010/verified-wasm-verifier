import HeytingLean.Numbers.Surreal.ReentryLoF
import HeytingLean.Quantum.SurrealVacuum

/-
Compile-only sanity checks for the surreal `VacuumOmegaRContext`.
-/

namespace HeytingLean.Tests.Numbers

open HeytingLean.Numbers
open HeytingLean.Numbers.Surreal
open HeytingLean.Quantum
open HeytingLean.Quantum.Surreal

-- Basic objects
#check surrealReentry
#check surrealVacuumContext

-- Specialised equivalence and birthday lemmas
#check surreal_vacuum_eq_euler
#check surreal_vacuum_birth_zero
#check surreal_vacuum_births_agree

end HeytingLean.Tests.Numbers

