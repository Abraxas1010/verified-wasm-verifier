import HeytingLean.Physics.FreeWill.Directions

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

abbrev OutcomeA : Type := Bool × Bool × Bool

namespace OutcomeA

@[simp] def x (o : OutcomeA) : Bool := o.1
@[simp] def y (o : OutcomeA) : Bool := o.2.1
@[simp] def z (o : OutcomeA) : Bool := o.2.2

end OutcomeA

/-- SPIN local law: every frame outcome is a permutation of `(1,1,0)`. -/
def SpinOutcome (o : OutcomeA) : Prop :=
  ExactlyOneFalse (OutcomeA.x o) (OutcomeA.y o) (OutcomeA.z o)

/-- SPIN law over deterministic A-wing responses. -/
def SpinAxiom {Dir : Type*} {Orth : Dir → Dir → Prop}
    (respA : Frame Dir Orth → OutcomeA) : Prop :=
  ∀ f, SpinOutcome (respA f)

/--
TWIN law in deterministic form: B agrees with A's coordinate result
for each direction in a chosen frame.
-/
def TwinAxiom {Dir : Type*} {Orth : Dir → Dir → Prop}
    (respA : Frame Dir Orth → OutcomeA) (respB : Dir → Bool) : Prop :=
  ∀ f,
    respB f.x = OutcomeA.x (respA f) ∧
    respB f.y = OutcomeA.y (respA f) ∧
    respB f.z = OutcomeA.z (respA f)

/--
Raw SPIN law at the accessible-information layer.
`respA` may be parameterized by both local frame and remote B-setting.
-/
def SpinAxiomRaw {InfoA Dir : Type*} {Orth : Dir → Dir → Prop}
    (chooseA : InfoA → Frame Dir Orth)
    (respA : InfoA → Frame Dir Orth → Dir → OutcomeA) : Prop :=
  ∀ iA w, SpinOutcome (respA iA (chooseA iA) w)

/--
Raw TWIN law at the accessible-information layer.
Agreement is only required at matched settings selected by `chooseA`/`chooseB`.
-/
def TwinAxiomRaw {InfoA InfoB Dir : Type*} {Orth : Dir → Dir → Prop}
    (chooseA : InfoA → Frame Dir Orth)
    (chooseB : InfoB → Dir)
    (respA : InfoA → Frame Dir Orth → Dir → OutcomeA)
    (respB : InfoB → Dir → Frame Dir Orth → Bool) : Prop :=
  ∀ iA iB,
    let f := chooseA iA
    let w := chooseB iB
    (w = f.x → respB iB w f = OutcomeA.x (respA iA f w)) ∧
    (w = f.y → respB iB w f = OutcomeA.y (respA iA f w)) ∧
    (w = f.z → respB iB w f = OutcomeA.z (respA iA f w))

end HeytingLean.Physics.FreeWill
