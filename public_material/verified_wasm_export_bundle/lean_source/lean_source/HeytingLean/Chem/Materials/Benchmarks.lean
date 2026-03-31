import HeytingLean.Chem.Materials.Crystal
import HeytingLean.Chem.Materials.Symmetry
import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem.Materials

open HeytingLean.Chem
open HeytingLean.Chem.PeriodicTable.Elements

def stdBasisVec {d : Nat} (i : Fin d) : FracCoord d :=
  fun j => if j = i then (1 : ℚ) else 0

def vec3 (a b c : ℚ) : FracCoord 3
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

def vec2 (a b : ℚ) : FracCoord 2
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

def siliconAtom : Atom := { element := Si, charge := 0 }
def sodiumAtom : Atom := { element := Na, charge := 0 }
def chlorineAtom : Atom := { element := Cl, charge := 0 }
def carbonAtom : Atom := { element := C, charge := 0 }

-- Silicon diamond cubic (conventional cell, minimal basis for a benchmark).
def siliconDiamond : UnitCell 3 :=
  { latticeVectors := stdBasisVec
    basis :=
      [ (vec3 0 0 0, siliconAtom)
      , (vec3 (1/4) (1/4) (1/4), siliconAtom)
      ]
  }

def siliconDiamondSpaceGroup : SpaceGroup := { label := "Fd-3m (placeholder)" }

-- NaCl rock-salt (simplified conventional cubic benchmark).
def sodiumChloride : UnitCell 3 :=
  { latticeVectors := stdBasisVec
    basis :=
      [ (vec3 0 0 0, sodiumAtom)
      , (vec3 (1/2) (1/2) (1/2), chlorineAtom)
      ]
  }

def sodiumChlorideSpaceGroup : SpaceGroup := { label := "Fm-3m (placeholder)" }

-- Graphene (2D benchmark): two-atom basis on a hex-like lattice; geometry is placeholder.
def graphene : UnitCell 2 :=
  { latticeVectors := stdBasisVec
    basis :=
      [ (vec2 0 0, carbonAtom)
      , (vec2 (1/3) (2/3), carbonAtom)
      ]
  }

def grapheneSpaceGroup : SpaceGroup := { label := "p6/mmm (placeholder)" }

end HeytingLean.Chem.Materials

