import HeytingLean.Chem.Bonding.Formula
import Mathlib.Data.Int.Basic

namespace HeytingLean.Chem

-- Minimal molecule: stoichiometric formula + net charge.
structure Molecule where
  formula : Formula
  charge : Int := 0

end HeytingLean.Chem
