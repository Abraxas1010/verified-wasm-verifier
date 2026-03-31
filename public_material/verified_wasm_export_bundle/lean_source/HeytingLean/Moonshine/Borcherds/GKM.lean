import HeytingLean.Moonshine.Monster.Construction

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine

universe u

/--
Gate-E (Borcherds) scaffold: data for a candidate generalized Kac-Moody side attached to
Moonshine construction core data.

This is intentionally lightweight and kernel-pure: it records only the interfaces that later
denominator/replication developments will consume.
-/
structure BorcherdsGKMData where
  C : MonsterConstructionCoreData
  L : Type u
  instAddCommGroup : AddCommGroup L
  instModule : Module ℂ L
  /-- Placeholder bracket operation for the superalgebra carrier. -/
  bracket : L → L → L
  /-- Coefficients expected to feed denominator/trace identities. -/
  gradingCoeff : C.S.M → ℤ → ℂ
  coeff_neg1 : ∀ g : C.S.M, gradingCoeff g (-1) = 1

attribute [instance] BorcherdsGKMData.instAddCommGroup BorcherdsGKMData.instModule

namespace BorcherdsGKMData

lemma gradingCoeff_id_neg1 (B : BorcherdsGKMData) :
    B.gradingCoeff (1 : B.C.S.M) (-1) = 1 :=
  B.coeff_neg1 1

end BorcherdsGKMData

end HeytingLean.Moonshine
