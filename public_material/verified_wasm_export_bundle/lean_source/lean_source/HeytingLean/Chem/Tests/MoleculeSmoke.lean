import HeytingLean.Chem.Bonding.Molecule
import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem
open HeytingLean.Chem.PeriodicTable.Elements

def waterFormula : Formula :=
  Formula.single H 2 + Formula.single O 1

def waterMolecule : Molecule := { formula := waterFormula, charge := 0 }

example : waterMolecule.charge = 0 := rfl
example : waterMolecule.formula.count H = 2 := by
  have hHO : (H : HeytingLean.Chem.PeriodicTable.Element) ≠ O := by decide
  simp [waterMolecule, waterFormula, Formula.count, Formula.single, hHO]

end HeytingLean.Chem.Tests
