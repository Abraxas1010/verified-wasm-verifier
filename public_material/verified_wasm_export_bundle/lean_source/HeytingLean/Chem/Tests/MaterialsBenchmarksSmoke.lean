import HeytingLean.Chem.Materials.Benchmarks

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem
open HeytingLean.Chem.Materials
open HeytingLean.Chem.PeriodicTable.Elements

example : siliconDiamond.numBasisAtoms = 2 := rfl

example : siliconDiamond.composition.count Si = 2 := by
  simp [UnitCell.composition, siliconDiamond, siliconAtom, Formula.count, Formula.single]

example : sodiumChloride.composition.count Na = 1 := by
  have hNaCl : (Na : HeytingLean.Chem.PeriodicTable.Element) ≠ Cl := by decide
  simp [UnitCell.composition, sodiumChloride, sodiumAtom, chlorineAtom, Formula.count, Formula.single, hNaCl]

example : sodiumChloride.composition.count Cl = 1 := by
  have hClNa : (Cl : HeytingLean.Chem.PeriodicTable.Element) ≠ Na := by decide
  simp [UnitCell.composition, sodiumChloride, sodiumAtom, chlorineAtom, Formula.count, Formula.single, hClNa]

example : graphene.numBasisAtoms = 2 := rfl

example : graphene.composition.count C = 2 := by
  simp [UnitCell.composition, graphene, carbonAtom, Formula.count, Formula.single]

end HeytingLean.Chem.Tests
