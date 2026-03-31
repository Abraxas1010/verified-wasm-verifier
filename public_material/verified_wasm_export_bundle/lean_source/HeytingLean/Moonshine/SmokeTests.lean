import HeytingLean.Moonshine.Modular.JSeries
import HeytingLean.Moonshine.Statement

set_option autoImplicit false

namespace HeytingLean.Moonshine

open scoped Classical

open HeytingLean.Moonshine.Modular

/-- Sanity checks on the hard-coded `J_q` coefficients. -/
example : J_qZ.coeff (-1) = (1 : ℤ) := coeff_J_qZ_neg1
example : J_qZ.coeff 0 = (0 : ℤ) := coeff_J_qZ_0
example : J_qZ.coeff 1 = (firstJCoeff : ℤ) := coeff_J_qZ_1
example : J_qZ.coeff 2 = (secondJCoeff : ℤ) := coeff_J_qZ_2

/-- McKay identity, as a Nat equality. -/
example : firstJCoeff = 1 + minFaithfulComplexRepDim := mckay_identity

/-
If `d` is a Monstrous Moonshine witness, then the identity-element Thompson series matches
`J_q` on degrees `-1,0,1,2` (at the level of these coefficients).
-/
section

variable {S : MonsterSpec}
variable (d : MonstrousMoonshineData S)

instance : Group S.M := S.instGroup

example : (ThompsonSeries d.V (1 : S.M)).coeff (-1) = (1 : ℂ) := by
  simp [ThompsonSeries_coeff, thompsonCoeff_one, d.dim_neg1]

example : (ThompsonSeries d.V (1 : S.M)).coeff 0 = (0 : ℂ) := by
  simp [ThompsonSeries_coeff, thompsonCoeff_one, d.dim_0]

example : (ThompsonSeries d.V (1 : S.M)).coeff 1 = (firstJCoeff : ℂ) := by
  simp [ThompsonSeries_coeff, thompsonCoeff_one, d.dim_1]

example : (ThompsonSeries d.V (1 : S.M)).coeff 2 = (secondJCoeff : ℂ) := by
  simp [ThompsonSeries_coeff, thompsonCoeff_one, d.dim_2]

end

end HeytingLean.Moonshine
