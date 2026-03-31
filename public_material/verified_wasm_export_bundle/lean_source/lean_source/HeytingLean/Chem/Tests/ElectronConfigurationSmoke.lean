import HeytingLean.Chem.PeriodicTable.ElectronConfiguration
import Mathlib.Tactic

/-!
# Electron-configuration smoke tests
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.PeriodicTable

example : electronCount (modelConfiguration 0) = 0 := by
  simp [modelConfiguration, fill]

example (Z : Nat) (hZ : Z ≤ 118) : electronCount (modelConfiguration Z) = Z := by
  simpa using electronCount_modelConfiguration_of_le Z hZ

end Tests
end Chem
end HeytingLean
