import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem.PeriodicTable
open HeytingLean.Chem.PeriodicTable.Elements

-- Spot-check a few element facts from the CIAAW 2024 table snapshot.
example : atomicNumber H = 1 := rfl
example : symbol H = "H" := rfl
example : name H = "hydrogen" := rfl

example : atomicNumber Fe = 26 := rfl
example : symbol Fe = "Fe" := rfl
example : name Fe = "iron" := rfl

example : atomicNumber Og = 118 := rfl
example : symbol Og = "Og" := rfl
example : name Og = "oganesson" := rfl

-- Sanity for lookups by atomic number.
example : ofAtomicNumber? 0 = none := by simp [ofAtomicNumber?]
example : (ofAtomicNumber? 26).map Fin.val = some 25 := rfl
example : ofAtomicNumber? 119 = none := by
  -- 119 -> m = 118, which is not < 118
  simp [ofAtomicNumber?]

end HeytingLean.Chem.Tests
