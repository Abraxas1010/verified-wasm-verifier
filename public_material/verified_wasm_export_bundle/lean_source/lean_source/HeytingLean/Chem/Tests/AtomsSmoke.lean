import HeytingLean.Chem.Bonding.Atoms
import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem
open HeytingLean.Chem.PeriodicTable.Elements

def ironAtom : Atom := { element := Fe, charge := 0 }

example : ironAtom.atomicNumber = 26 := rfl
example : ironAtom.symbol = "Fe" := rfl
example : ironAtom.name = "iron" := rfl

end HeytingLean.Chem.Tests

