import HeytingLean.LoF.ICC.GPUVerifier

namespace HeytingLean.Tests.LoF

open HeytingLean.LoF
open HeytingLean.LoF.ICC
open HeytingLean.LoF.LoFPrimary

#check WitnessLaw
#check TinyLawWitness
#check encodePrimaryFixture
#check callingWitness
#check crossingWitness
#check accepts

example : (encodePrimaryFixture Expr.void).annFree = true := by
  simp

example : Term.Closed (encodePrimaryFixture (.juxt .void (.mark .void))) := by
  simp

example : step? (callingCertificate (encodePrimaryFixture Expr.void)) =
    some (encodePrimaryFixture Expr.void) := by
  native_decide

example : step? (crossingCertificate (encodePrimaryFixture (.mark .void))) =
    some (encodePrimaryFixture (.mark .void)) := by
  native_decide

example : (callingWitness (.mark .void)).source = Expr.juxt (.mark .void) (.mark .void) := by
  rfl

example : (crossingWitness (.juxt .void (.mark .void))).source =
    Expr.mark (Expr.mark (.juxt .void (.mark .void))) := by
  rfl

example : accepts callingVoid := by
  exact callingWitness_accepts _

example : accepts callingMarkedVoid := by
  exact callingWitness_accepts _

example : accepts crossingVoid := by
  exact crossingWitness_accepts _

example : accepts crossingJuxtVoidMarkedVoid := by
  exact crossingWitness_accepts _

example : witnessFixtures.length = 4 := by
  rfl

example : witnessFixtures.map Prod.fst =
    [ "calling_void"
    , "calling_marked_void"
    , "crossing_void"
    , "crossing_juxt_void_marked_void"
    ] := by
  rfl

end HeytingLean.Tests.LoF
