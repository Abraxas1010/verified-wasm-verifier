import HeytingLean.Physics.FreeWill.FreeWillTheorem

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

/--
Internal operational package for the Free-Will lane:
all assumptions needed by `free_will_core` are bundled as first-class data.
-/
structure OperationalModel where
  InfoA : Type*
  InfoB : Type*
  chooseA : InfoA → PeresFrame
  chooseB : InfoB → Dir
  respA : InfoA → PeresFrame → Dir → OutcomeA
  respB : InfoB → Dir → PeresFrame → Bool
  hFreeA : FreeChoiceA chooseA
  hFreeB : FreeChoiceB chooseB
  hMIN : MIN respA respB
  hSpinRaw : SpinAxiomRaw chooseA respA
  hTwinRaw : TwinAxiomRaw chooseA chooseB respA respB

theorem contradiction_of_operationalModel (M : OperationalModel) : False := by
  exact free_will_core M.chooseA M.chooseB M.hFreeA M.hFreeB M.respA M.respB M.hMIN M.hSpinRaw M.hTwinRaw

/--
Internal endpoint (no external bridge function):
if an operational model exists, predictability is impossible.
-/
theorem not_predictable_internal
    {World Past Outcome : Type*}
    (past : World → Past)
    (out : World → Outcome)
    (M : OperationalModel) :
    ¬ Predictable past out := by
  intro _hPred
  exact contradiction_of_operationalModel M

/--
Internal unmarked-future endpoint (no external bridge function):
derived directly from the internal `OperationalModel`.
-/
theorem unmarked_future_internal
    {World Past Outcome : Type*}
    (past : World → Past)
    (out : World → Outcome)
    (M : OperationalModel) :
    UnmarkedFuture past out := by
  exact unmarkedFuture_of_not_predictable past out (not_predictable_internal past out M)

/--
Compatibility adapter: build an internal operational model from tuple fields.
-/
def mkOperationalModel
    {InfoA InfoB : Type*}
    (chooseA : InfoA → PeresFrame)
    (chooseB : InfoB → Dir)
    (respA : InfoA → PeresFrame → Dir → OutcomeA)
    (respB : InfoB → Dir → PeresFrame → Bool)
    (hFreeA : FreeChoiceA chooseA)
    (hFreeB : FreeChoiceB chooseB)
    (hMIN : MIN respA respB)
    (hSpinRaw : SpinAxiomRaw chooseA respA)
    (hTwinRaw : TwinAxiomRaw chooseA chooseB respA respB) :
    OperationalModel :=
  { InfoA := InfoA
    InfoB := InfoB
    chooseA := chooseA
    chooseB := chooseB
    respA := respA
    respB := respB
    hFreeA := hFreeA
    hFreeB := hFreeB
    hMIN := hMIN
    hSpinRaw := hSpinRaw
    hTwinRaw := hTwinRaw }

/--
Compatibility theorem with the previous bridge-shaped API.
Internally it routes through `mkOperationalModel` + `unmarked_future_internal`.
-/
theorem unmarked_future_via_internal
    {World Past Outcome InfoA InfoB : Type*}
    (past : World → Past)
    (out : World → Outcome)
    (hBridge :
      Predictable past out →
      ∃ (chooseA : InfoA → PeresFrame) (chooseB : InfoB → Dir)
        (respA : InfoA → PeresFrame → Dir → OutcomeA)
        (respB : InfoB → Dir → PeresFrame → Bool),
        FreeChoiceA chooseA ∧
        FreeChoiceB chooseB ∧
        MIN respA respB ∧
        SpinAxiomRaw chooseA respA ∧
        TwinAxiomRaw chooseA chooseB respA respB) :
    UnmarkedFuture past out := by
  by_cases hPred : Predictable past out
  · rcases hBridge hPred with
      ⟨chooseA, chooseB, respA, respB, hFreeA, hFreeB, hMIN, hSpinRaw, hTwinRaw⟩
    let M :=
      mkOperationalModel chooseA chooseB respA respB hFreeA hFreeB hMIN hSpinRaw hTwinRaw
    exact unmarked_future_internal past out M
  · exact unmarkedFuture_of_not_predictable past out hPred

end HeytingLean.Physics.FreeWill
