import HeytingLean.Discovery

namespace HeytingLean.Tests.Discovery

open HeytingLean.Discovery.SRTranslation
open HeytingLean.Discovery.RankNullityPremises

def chiExpr : SRExpr :=
  .binop .eq
    (.binop .add
      (.binop .sub (.var .height_d1) (.var .width_d1))
      (.var .width_d2))
    (.lit 2)

example : renderVar .height_d1 = "height_d1" := rfl

example : render chiExpr = "(((height_d1 - width_d1) + width_d2) = 2)" := rfl

example : featureArity chiExpr = 3 := by
  native_decide

example
    {R V0 V1 V2 : Type*}
    [DivisionRing R]
    [AddCommGroup V0] [Module R V0] [FiniteDimensional R V0]
    [AddCommGroup V1] [Module R V1] [FiniteDimensional R V1]
    [AddCommGroup V2] [Module R V2] [FiniteDimensional R V2]
    (D1 : V1 →ₗ[R] V0) (D2 : V2 →ₗ[R] V1)
    (h1 : rankNullityD1 (R := R) (V0 := V0) (V1 := V1) D1)
    (h2 : rankNullityD2 (R := R) (V1 := V1) (V2 := V2) D2)
    (h3 : connectedSurface (R := R) (V0 := V0) (V1 := V1) D1)
    (h4 : orientableSurface (R := R) (V1 := V1) (V2 := V2) D2)
    (h5 : vanishingMiddleBetti (R := R) (V0 := V0) (V1 := V1) (V2 := V2) D1 D2) :
    (Module.finrank R V0 : Int) - (Module.finrank R V1 : Int) + (Module.finrank R V2 : Int) = 2 := by
  exact sphereEuler (R := R) (D1 := D1) (D2 := D2) h1 h2 h3 h4 h5

end HeytingLean.Tests.Discovery

