import HeytingLean.Chem.Bonding.Formula

/-!
# Stoichiometric reactions (formula-level)

This module models chemical reactions at the level of stoichiometric formulas:
reactants and products are lists of `(coefficient, formula)`.

Balancing is expressed as equality of total element counts.
-/

namespace HeytingLean.Chem.Reactions

open HeytingLean.Chem

structure StoichTerm where
  coeff : Nat
  formula : Formula

namespace StoichTerm

def totalFormula (t : StoichTerm) : Formula :=
  t.coeff • t.formula

end StoichTerm

def total (ts : List StoichTerm) : Formula :=
  ts.foldl (fun acc t => acc + t.totalFormula) 0

def Balanced (reactants products : List StoichTerm) : Prop :=
  total reactants = total products

end HeytingLean.Chem.Reactions

