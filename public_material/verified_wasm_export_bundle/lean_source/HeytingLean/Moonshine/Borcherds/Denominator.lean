import HeytingLean.Moonshine.Borcherds.GKM
import HeytingLean.Moonshine.Modular.JSeries
import HeytingLean.Moonshine.ThompsonSeries

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine

/--
Gate-E denominator interface.

`denominatorSeries` is the formal output of the Borcherds-side denominator package, and
`denominator_eq_thompson` is the key bridge to the Thompson series coming from the graded
representation data.
-/
structure DenominatorIdentityData where
  B : BorcherdsGKMData
  denominatorSeries : B.C.S.M → Modular.Laurent ℂ
  denominator_eq_thompson : ∀ g : B.C.S.M, denominatorSeries g = ThompsonSeries B.C.V g

namespace DenominatorIdentityData

lemma denominator_coeff_eq_thompsonCoeff
    (D : DenominatorIdentityData) (g : D.B.C.S.M) (n : ℤ) :
    (D.denominatorSeries g).coeff n = thompsonCoeff D.B.C.V g n := by
  rw [D.denominator_eq_thompson g, ThompsonSeries_coeff]

/--
Identity-element denominator coefficients are determined by the Gate-D core dimensions.
-/
theorem denominatorSeries_one_coeffs
    (D : DenominatorIdentityData) :
    (D.denominatorSeries (1 : D.B.C.S.M)).coeff (-1) = (1 : ℂ) ∧
    (D.denominatorSeries (1 : D.B.C.S.M)).coeff 0 = (0 : ℂ) ∧
    (D.denominatorSeries (1 : D.B.C.S.M)).coeff 1 = (firstJCoeff : ℂ) ∧
    (D.denominatorSeries (1 : D.B.C.S.M)).coeff 2 = (secondJCoeff : ℂ) := by
  rcases D.B.C.thompsonSeries_one_coeffs with ⟨hneg1, h0, h1, h2⟩
  constructor
  · simpa [D.denominator_eq_thompson 1] using hneg1
  constructor
  · simpa [D.denominator_eq_thompson 1] using h0
  constructor
  · simpa [D.denominator_eq_thompson 1] using h1
  · simpa [D.denominator_eq_thompson 1] using h2

/-- Identity-element denominator coefficients matched to `J_q`. -/
theorem denominatorSeries_one_coeffs_match_J_q
    (D : DenominatorIdentityData) :
    (D.denominatorSeries (1 : D.B.C.S.M)).coeff (-1) = Modular.J_q.coeff (-1) ∧
    (D.denominatorSeries (1 : D.B.C.S.M)).coeff 0 = Modular.J_q.coeff 0 ∧
    (D.denominatorSeries (1 : D.B.C.S.M)).coeff 1 = Modular.J_q.coeff 1 ∧
    (D.denominatorSeries (1 : D.B.C.S.M)).coeff 2 = Modular.J_q.coeff 2 := by
  rcases D.denominatorSeries_one_coeffs with ⟨hneg1, h0, h1, h2⟩
  constructor
  · simpa [Modular.coeff_J_q_neg1] using hneg1
  constructor
  · simpa [Modular.coeff_J_q_0] using h0
  constructor
  · simpa [Modular.coeff_J_q_1] using h1
  · simpa [Modular.coeff_J_q_2] using h2

end DenominatorIdentityData

end HeytingLean.Moonshine
