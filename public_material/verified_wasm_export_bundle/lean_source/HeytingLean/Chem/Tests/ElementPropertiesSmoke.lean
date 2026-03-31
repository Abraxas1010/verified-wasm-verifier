import HeytingLean.Chem.PeriodicTable.Properties
import HeytingLean.Chem.PeriodicTable.Elements
import Mathlib.Tactic

/-!
# Element-properties smoke tests

These tests are compile-only and use `native_decide` for a small number of
concrete sanity checks.
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.PeriodicTable
open HeytingLean.Chem.PeriodicTable.Elements

example : (modelProperties H).atomicNumber = 1 := by
  native_decide

example : (modelProperties H).period = 1 := by
  native_decide

example : (modelProperties He).iupacGroup? = some 18 := by
  native_decide

example : (modelProperties Fe).block = Orbital.d := by
  native_decide

end Tests
end Chem
end HeytingLean

