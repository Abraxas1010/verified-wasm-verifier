import HeytingLean.Chem.Foundations.Terms
import HeytingLean.Chem.Foundations.Constants
import HeytingLean.Chem.Bonding.Definitions
import HeytingLean.Chem.QED.Dirac
import HeytingLean.Chem.QED.BoundState.RadiativePotentials

/-!
# QED chemistry smoke test

Compile-only test: checks that the new `Chem/` modules are importable together and that the
provenance-first objects are definable without proof holes.
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.Foundations
open HeytingLean.Chem.Bonding
open HeytingLean.Chem.QED.BoundState

example : chemicalBondTerm.name = "chemical bond" := by
  rfl

example : uehling.tag = RadiativeCorrection.vacuumPolarization := by
  rfl

example : cLight.symbol = "c" := by
  rfl

end Tests
end Chem
end HeytingLean
