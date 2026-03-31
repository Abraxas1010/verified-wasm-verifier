import HeytingLean.Moonshine.MoonshineModule.VNatural
import HeytingLean.Moonshine.Statement

set_option autoImplicit false

namespace HeytingLean.Moonshine

universe u

/--
Gate-D core bridge object: packages construction-side data up to the graded module and the
first required coefficient constraints.

This intentionally stops short of the Hauptmodul conclusion so later Borcherds/replication
layers can derive it and then repackage the full statement witness.
-/
structure MonsterConstructionCoreData where
  Vn : VNaturalData
  S : MonsterSpec.{u}
  V : GradedRep.{u, u} S.M
  dim_neg1 : gradedDim V (-1) = 1
  dim_0 : gradedDim V 0 = 0
  dim_1 : gradedDim V 1 = firstJCoeff
  dim_2 : gradedDim V 2 = secondJCoeff

/--
Gate-D bridge object: packages a candidate Monster construction from `V^natural`-side data
into the exact fields required by the Moonshine statement layer.

This module is kernel-pure and assumption-explicit: no global existence claim is made.
-/
structure MonsterConstructionData extends MonsterConstructionCoreData where
  thompson_is_hauptmodul :
    ∀ g : S.M, ∃ H : HauptmodulData S.M, H.qExp = ThompsonSeries V g

namespace MonsterConstructionCoreData

/--
Identity-element Thompson-series coefficients forced by the Gate-D core dimension constraints.
-/
theorem thompsonSeries_one_coeffs
    (C : MonsterConstructionCoreData) :
    (ThompsonSeries C.V (1 : C.S.M)).coeff (-1) = (1 : ℂ) ∧
    (ThompsonSeries C.V (1 : C.S.M)).coeff 0 = (0 : ℂ) ∧
    (ThompsonSeries C.V (1 : C.S.M)).coeff 1 = (firstJCoeff : ℂ) ∧
    (ThompsonSeries C.V (1 : C.S.M)).coeff 2 = (secondJCoeff : ℂ) := by
  constructor
  · simpa [ThompsonSeries_coeff, thompsonCoeff_one] using congrArg (fun n : Nat => (n : ℂ)) C.dim_neg1
  constructor
  · simpa [ThompsonSeries_coeff, thompsonCoeff_one] using congrArg (fun n : Nat => (n : ℂ)) C.dim_0
  constructor
  · simpa [ThompsonSeries_coeff, thompsonCoeff_one] using congrArg (fun n : Nat => (n : ℂ)) C.dim_1
  · simpa [ThompsonSeries_coeff, thompsonCoeff_one] using congrArg (fun n : Nat => (n : ℂ)) C.dim_2

/-- Identity-element Thompson-series coefficients in `J_q` form. -/
theorem thompsonSeries_one_coeffs_match_J_q
    (C : MonsterConstructionCoreData) :
    (ThompsonSeries C.V (1 : C.S.M)).coeff (-1) = Modular.J_q.coeff (-1) ∧
    (ThompsonSeries C.V (1 : C.S.M)).coeff 0 = Modular.J_q.coeff 0 ∧
    (ThompsonSeries C.V (1 : C.S.M)).coeff 1 = Modular.J_q.coeff 1 ∧
    (ThompsonSeries C.V (1 : C.S.M)).coeff 2 = Modular.J_q.coeff 2 := by
  rcases C.thompsonSeries_one_coeffs with ⟨hneg1, h0, h1, h2⟩
  constructor
  · simpa [Modular.coeff_J_q_neg1] using hneg1
  constructor
  · simpa [Modular.coeff_J_q_0] using h0
  constructor
  · simpa [Modular.coeff_J_q_1] using h1
  · simpa [Modular.coeff_J_q_2] using h2

end MonsterConstructionCoreData

namespace MonsterConstructionData

/-- Drop the Hauptmodul witness and keep only the core construction package. -/
def toCore (C : MonsterConstructionData) : MonsterConstructionCoreData where
  Vn := C.Vn
  S := C.S
  V := C.V
  dim_neg1 := C.dim_neg1
  dim_0 := C.dim_0
  dim_1 := C.dim_1
  dim_2 := C.dim_2

/-- Forgetful map from construction package to the statement-level witness bundle. -/
def toMonstrousMoonshineData (C : MonsterConstructionData) : MonstrousMoonshineData C.S where
  V := C.V
  dim_neg1 := C.dim_neg1
  dim_0 := C.dim_0
  dim_1 := C.dim_1
  dim_2 := C.dim_2
  thompson_is_hauptmodul := C.thompson_is_hauptmodul

/-- Any such construction package immediately proves the headline Moonshine statement. -/
theorem statement (C : MonsterConstructionData) : MonstrousMoonshineStatement C.S := by
  refine ⟨?_⟩
  exact
    { V := C.V
      dim_neg1 := C.dim_neg1
      dim_0 := C.dim_0
      dim_1 := C.dim_1
      dim_2 := C.dim_2
      thompson_is_hauptmodul := C.thompson_is_hauptmodul }

/--
For the identity element, Gate-D provides a Hauptmodul witness whose `q`-expansion agrees with
`J_q` on coefficients `-1,0,1,2`.
-/
theorem exists_hauptmodul_one_qExp_coeffs_match_J_q
    (C : MonsterConstructionData) :
    ∃ H : HauptmodulData C.S.M,
      H.qExp = ThompsonSeries C.V (1 : C.S.M) ∧
      H.qExp.coeff (-1) = Modular.J_q.coeff (-1) ∧
      H.qExp.coeff 0 = Modular.J_q.coeff 0 ∧
      H.qExp.coeff 1 = Modular.J_q.coeff 1 ∧
      H.qExp.coeff 2 = Modular.J_q.coeff 2 := by
  rcases C.thompson_is_hauptmodul 1 with ⟨H, hH⟩
  refine ⟨H, hH, ?_⟩
  rcases C.toCore.thompsonSeries_one_coeffs_match_J_q with ⟨hneg1, h0, h1, h2⟩
  constructor
  · simpa [hH] using hneg1
  constructor
  · simpa [hH] using h0
  constructor
  · simpa [hH] using h1
  · simpa [hH] using h2

end MonsterConstructionData

end HeytingLean.Moonshine
