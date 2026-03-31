import HeytingLean.Moonshine.SmokeTests

set_option autoImplicit false

namespace HeytingLean.Moonshine

open scoped Classical

open HeytingLean.Moonshine.Modular

section

variable {S : MonsterSpec}
variable (d : MonstrousMoonshineData S)

instance : Group S.M := S.instGroup

theorem thompsonSeries_one_coeffs_match_J_q :
    (ThompsonSeries d.V (1 : S.M)).coeff (-1) = J_q.coeff (-1) ∧
    (ThompsonSeries d.V (1 : S.M)).coeff 0 = J_q.coeff 0 ∧
    (ThompsonSeries d.V (1 : S.M)).coeff 1 = J_q.coeff 1 ∧
    (ThompsonSeries d.V (1 : S.M)).coeff 2 = J_q.coeff 2 := by
  constructor
  · simp [coeff_J_q_neg1, ThompsonSeries_coeff, thompsonCoeff_one, d.dim_neg1]
  constructor
  · simp [coeff_J_q_0, ThompsonSeries_coeff, thompsonCoeff_one, d.dim_0]
  constructor
  · simp [coeff_J_q_1, ThompsonSeries_coeff, thompsonCoeff_one, d.dim_1]
  · simp [coeff_J_q_2, ThompsonSeries_coeff, thompsonCoeff_one, d.dim_2]

end

end HeytingLean.Moonshine
