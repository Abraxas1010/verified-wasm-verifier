import HeytingLean.Chem.Materials.Crystal
import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem
open HeytingLean.Chem.Materials
open HeytingLean.Chem.PeriodicTable.Elements

def stdBasisVec (i : Fin 3) : FracCoord 3 :=
  fun j => if j = i then (1 : ℚ) else 0

def siliconAtom : Atom := { element := Si, charge := 0 }

def simpleCubic : UnitCell 3 :=
  { latticeVectors := stdBasisVec
    basis := [(fun _ => (0 : ℚ), siliconAtom)]
  }

example : simpleCubic.numBasisAtoms = 1 := rfl

end HeytingLean.Chem.Tests

