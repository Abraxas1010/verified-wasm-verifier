import HeytingLean.Chem.Bonding.Formula
import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem
open HeytingLean.Chem.PeriodicTable
open HeytingLean.Chem.PeriodicTable.Elements

def water : Formula :=
  Formula.single H 2 + Formula.single O 1

example : water.count H = 2 := by
  have hHO : (H : Element) ≠ O := by decide
  simp [water, Formula.count, Formula.single, hHO]

example : water.count O = 1 := by
  have hOH : (O : Element) ≠ H := by decide
  simp [water, Formula.count, Formula.single, hOH]

example : water.count Fe = 0 := by
  have hFeH : (Fe : Element) ≠ H := by decide
  have hFeO : (Fe : Element) ≠ O := by decide
  simp [water, Formula.count, Formula.single, hFeH, hFeO]

end HeytingLean.Chem.Tests
