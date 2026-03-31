import HeytingLean.Moonshine.GradedRep
import HeytingLean.Moonshine.Hauptmodul
import HeytingLean.Moonshine.Monster.Constants
import HeytingLean.Moonshine.Monster.Spec
import HeytingLean.Moonshine.ThompsonSeries

set_option autoImplicit false

namespace HeytingLean.Moonshine

universe u

/--
A concrete witness bundle for the (Borcherds-style) Monstrous Moonshine headline statement.

This is intentionally an interface: no axioms, no claim of existence.
-/
structure MonstrousMoonshineData (S : MonsterSpec.{u}) : Type (u + 1) where
  V : GradedRep S.M
  dim_neg1 : gradedDim V (-1) = 1
  dim_0 : gradedDim V 0 = 0
  dim_1 : gradedDim V 1 = firstJCoeff
  dim_2 : gradedDim V 2 = secondJCoeff
  thompson_is_hauptmodul :
    ∀ g : S.M, ∃ H : HauptmodulData S.M, H.qExp = ThompsonSeries V g

/-- The Monstrous Moonshine headline statement as a `Prop`. -/
def MonstrousMoonshineStatement (S : MonsterSpec.{u}) : Prop :=
  Nonempty (MonstrousMoonshineData (S := S))

end HeytingLean.Moonshine
