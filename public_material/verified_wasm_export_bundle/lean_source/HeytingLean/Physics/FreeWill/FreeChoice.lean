import HeytingLean.Physics.FreeWill.KochenSpecker

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

/-- Free choice for A: every frame can be selected from accessible info. -/
def FreeChoiceA {InfoA : Type*} (chooseA : InfoA → PeresFrame) : Prop :=
  ∀ f : PeresFrame, ∃ i : InfoA, chooseA i = f

/-- Free choice for B: every direction can be selected from accessible info. -/
def FreeChoiceB {InfoB : Type*} (chooseB : InfoB → Dir) : Prop :=
  ∀ w : Dir, ∃ i : InfoB, chooseB i = w

end HeytingLean.Physics.FreeWill
