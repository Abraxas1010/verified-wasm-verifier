import HeytingLean.Chem.Foundations.Nuclide

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem
open HeytingLean.Chem.PeriodicTable.Elements

def carbon12 : Nuclide := { element := C, massNumber := 12 }

example : carbon12.atomicNumber = 6 := rfl
example : carbon12.neutronNumber = 6 := by
  have hC : HeytingLean.Chem.PeriodicTable.atomicNumber C = 6 := rfl
  simp [carbon12, Nuclide.neutronNumber, Nuclide.atomicNumber, hC]

end HeytingLean.Chem.Tests
