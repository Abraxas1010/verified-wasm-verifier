import HeytingLean.Chem.Interactions.ForceField
import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem
open HeytingLean.Chem.Interactions
open HeytingLean.Chem.PeriodicTable.Elements

def dummyAtom : Atom := { element := He, charge := 0 }

def cfg1 : Configuration 1 :=
  { atoms := fun _ => dummyAtom
    dist := fun _ _ => 0
  }

def ff0 : ForceField := { pair := fun _ _ _ => 0 }

example : totalPairEnergy ff0 cfg1 = 0 := by
  -- No pairs for n=1, so the sum is empty.
  simp [totalPairEnergy, pairIndexSet, cfg1, ff0]

end HeytingLean.Chem.Tests
