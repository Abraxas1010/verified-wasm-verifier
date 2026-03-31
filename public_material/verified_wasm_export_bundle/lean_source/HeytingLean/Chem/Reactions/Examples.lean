import HeytingLean.Chem.Reactions.Reaction
import HeytingLean.Chem.PeriodicTable.Elements
import Mathlib.Tactic

/-!
# Stoichiometry examples
-/

namespace HeytingLean.Chem.Reactions.Examples

open HeytingLean.Chem
open HeytingLean.Chem.Reactions
open HeytingLean.Chem.PeriodicTable.Elements

def H2 : Formula := Formula.single H 2
def O2 : Formula := Formula.single O 2
def H2O : Formula := Formula.single H 2 + Formula.single O 1

def CO2 : Formula := Formula.single C 1 + Formula.single O 2
def CH4 : Formula := Formula.single C 1 + Formula.single H 4

-- 2 H2 + O2 -> 2 H2O
theorem water_is_balanced : Balanced
    [ { coeff := 2, formula := H2 }, { coeff := 1, formula := O2 } ]
    [ { coeff := 2, formula := H2O } ] := by
  unfold Balanced
  funext e
  simp [total, StoichTerm.totalFormula, H2, O2, H2O, Formula.single]
  by_cases hH : e = H
  · subst hH
    have hHO : H ≠ O := by native_decide
    simp [hHO]
  · by_cases hO : e = O
    · subst hO
      simp [hH]
    · simp [hH, hO]

-- CH4 + 2 O2 -> CO2 + 2 H2O
theorem methane_combustion_is_balanced : Balanced
    [ { coeff := 1, formula := CH4 }, { coeff := 2, formula := O2 } ]
    [ { coeff := 1, formula := CO2 }, { coeff := 2, formula := H2O } ] := by
  unfold Balanced
  funext e
  simp [total, StoichTerm.totalFormula, CH4, O2, CO2, H2O, Formula.single]
  by_cases hC : e = C
  · subst hC
    have hCH : C ≠ H := by native_decide
    have hCO : C ≠ O := by native_decide
    simp [hCH, hCO]
  · by_cases hH : e = H
    · subst hH
      have hHO : H ≠ O := by native_decide
      simp [hC, hHO]
    · by_cases hO : e = O
      · subst hO
        simp [hC, hH]
      · simp [hC, hH, hO]

end HeytingLean.Chem.Reactions.Examples
