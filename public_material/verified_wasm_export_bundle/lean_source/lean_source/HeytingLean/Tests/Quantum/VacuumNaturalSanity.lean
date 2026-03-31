import HeytingLean.Quantum.OMLCat
import HeytingLean.LoF.HeytingCat
import HeytingLean.Quantum.VacuumNatural

/-
Compile-only sanity checks for the categorical vacuum/naturality layer.
These tests ensure that the new bundled categories and functors are in
scope and that the basic constructions typecheck.
-/

namespace HeytingLean
namespace Quantum
namespace Tests

open HeytingLean.Quantum
open HeytingLean.Quantum.OMLCat
open HeytingLean.LoF

-- Basic objects and functors should be available.
#check OMLCat
#check HeytingCat
#check VacuumCat
#check VacuumCat.ForgetVacuumToOML
#check VacuumCat.ForgetVacuumToHeyt
#check VacuumCat.QLFunctor

-- Ωᴿ-level carriers and morphisms.
#check VacuumCat.OmegaCarrier
#check VacuumCat.OmegaMap
#check VacuumCat.vacuumAt
#check VacuumCat.eulerAt

-- Compatibility and naturality predicates.
#check VacuumCat.VacuumCompatible
#check VacuumCat.vacuum_natural
#check VacuumCat.VacuumMor
#check VacuumCat.VacuumMor.euler_natural

-- Concrete QGI example bundles into a `VacuumObj`.
#check VacuumCat.qgiObj
#check VacuumCat.qgi_euler_agrees

end Tests
end Quantum
end HeytingLean

