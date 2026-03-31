import HeytingLean.Chem.PeriodicTable.ExabyteProperties
import HeytingLean.Chem.PeriodicTable.Elements
import Mathlib.Tactic

/-!
# Exabyte periodic-table properties smoke tests

Compile-only checks for the Exabyte periodic-table dataset integration.
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.PeriodicTable
open HeytingLean.Chem.PeriodicTable.Elements

example : (exabyteInfo H).name = "Hydrogen" := by
  native_decide

example : (exabyteInfo Og).atomicNumber = 118 := by
  native_decide

example : (exabyteInfo F).paulingNegativity = some "3.98" := by
  native_decide

example : (exabyteInfo Fe).density_g_per_cm3 = some "7.874" := by
  native_decide

example : exabyteAtomicNumber H = atomicNumber H := by
  simpa using exabyte_atomicNumber_matches H

end Tests
end Chem
end HeytingLean
