import HeytingLean.Chem.Bonding.Atoms
import HeytingLean.Chem.Bonding.Formula
import Mathlib.Data.Rat.Defs

namespace HeytingLean.Chem.Materials

open HeytingLean.Chem

-- Fractional coordinates in a d-dimensional unit cell.
abbrev FracCoord (d : Nat) : Type := Fin d -> ℚ

-- A minimal unit-cell record: lattice vectors (in fractional coords) + a basis of atoms.
structure UnitCell (d : Nat) where
  latticeVectors : Fin d -> FracCoord d
  basis : List (FracCoord d × Atom)

def UnitCell.numBasisAtoms {d : Nat} (uc : UnitCell d) : Nat :=
  uc.basis.length

-- Stoichiometric composition implied by the basis (one count per basis atom).
def UnitCell.composition {d : Nat} (uc : UnitCell d) : Formula :=
  uc.basis.foldl
    (fun f p => f + Formula.single p.2.element 1)
    0

end HeytingLean.Chem.Materials
