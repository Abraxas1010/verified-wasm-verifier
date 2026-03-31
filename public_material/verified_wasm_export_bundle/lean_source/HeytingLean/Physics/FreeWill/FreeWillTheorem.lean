import HeytingLean.Physics.FreeWill.Axioms
import HeytingLean.Physics.FreeWill.FreeChoice
import HeytingLean.Physics.FreeWill.KochenSpecker
import HeytingLean.Physics.FreeWill.Relativity
import HeytingLean.Physics.FreeWill.RelativisticForcing

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

/-- SPIN + TWIN force a global 101 valuation, contradicting Kochen-Specker. -/
theorem no_deterministic_model
    (respA : PeresFrame → OutcomeA)
    (respB : Dir → Bool)
    (hSpin : SpinAxiom respA)
    (hTwin : TwinAxiom respA respB) :
    False := by
  have h101 : Is101 Orth respB := by
    intro f
    have hSpinF : SpinOutcome (respA f) := hSpin f
    rcases hTwin f with ⟨hx, hy, hz⟩
    unfold SpinOutcome at hSpinF
    simpa [hx, hy, hz] using hSpinF
  exact no101_peres33 ⟨respB, h101⟩

noncomputable def chooseInfoA {InfoA : Type*}
    (chooseA : InfoA → PeresFrame) (hFreeA : FreeChoiceA chooseA)
    (f : PeresFrame) : InfoA :=
  Classical.choose (hFreeA f)

@[simp] theorem chooseInfoA_spec {InfoA : Type*}
    (chooseA : InfoA → PeresFrame) (hFreeA : FreeChoiceA chooseA)
    (f : PeresFrame) :
    chooseA (chooseInfoA chooseA hFreeA f) = f :=
  Classical.choose_spec (hFreeA f)

noncomputable def chooseInfoB {InfoB : Type*}
    (chooseB : InfoB → Dir) (hFreeB : FreeChoiceB chooseB)
    (w : Dir) : InfoB :=
  Classical.choose (hFreeB w)

@[simp] theorem chooseInfoB_spec {InfoB : Type*}
    (chooseB : InfoB → Dir) (hFreeB : FreeChoiceB chooseB)
    (w : Dir) :
    chooseB (chooseInfoB chooseB hFreeB w) = w :=
  Classical.choose_spec (hFreeB w)

/--
Deterministic A-wing response extracted from the operational model:
pick the `InfoA` witness of frame `f` and evaluate at remote setting `f.x`.
-/
noncomputable def detRespA
    {InfoA : Type*}
    (chooseA : InfoA → PeresFrame)
    (hFreeA : FreeChoiceA chooseA)
    (respA : InfoA → PeresFrame → Dir → OutcomeA) :
    PeresFrame → OutcomeA := fun f =>
  respA (chooseInfoA chooseA hFreeA f) f f.x

/--
Deterministic B-wing response extracted from the operational model:
pick the `InfoB` witness of direction `w`; remote frame argument is fixed and
later eliminated via `MIN`.
-/
noncomputable def detRespB
    {InfoB : Type*}
    (chooseB : InfoB → Dir)
    (hFreeB : FreeChoiceB chooseB)
    (respB : InfoB → Dir → PeresFrame → Bool) :
    Dir → Bool := fun w =>
  respB (chooseInfoB chooseB hFreeB w) w (default : PeresFrame)

theorem detRespA_spin
    {InfoA : Type*}
    (chooseA : InfoA → PeresFrame)
    (hFreeA : FreeChoiceA chooseA)
    (respA : InfoA → PeresFrame → Dir → OutcomeA)
    (hSpinRaw : SpinAxiomRaw chooseA respA) :
    SpinAxiom (detRespA chooseA hFreeA respA) := by
  intro f
  have h := hSpinRaw (chooseInfoA chooseA hFreeA f) f.x
  simpa [detRespA, chooseInfoA_spec] using h

theorem detResp_twin
    {InfoA InfoB : Type*}
    (chooseA : InfoA → PeresFrame)
    (chooseB : InfoB → Dir)
    (hFreeA : FreeChoiceA chooseA)
    (hFreeB : FreeChoiceB chooseB)
    (respA : InfoA → PeresFrame → Dir → OutcomeA)
    (respB : InfoB → Dir → PeresFrame → Bool)
    (hMIN : MIN respA respB)
    (hTwinRaw : TwinAxiomRaw chooseA chooseB respA respB) :
    TwinAxiom (detRespA chooseA hFreeA respA) (detRespB chooseB hFreeB respB) := by
  intro f
  let iA := chooseInfoA chooseA hFreeA f
  let iBx := chooseInfoB chooseB hFreeB f.x
  let iBy := chooseInfoB chooseB hFreeB f.y
  let iBz := chooseInfoB chooseB hFreeB f.z

  have hiA : chooseA iA = f := by
    simp [iA, chooseInfoA_spec]
  have hiBx : chooseB iBx = f.x := by
    simp [iBx, chooseInfoB_spec]
  have hiBy : chooseB iBy = f.y := by
    simp [iBy, chooseInfoB_spec]
  have hiBz : chooseB iBz = f.z := by
    simp [iBz, chooseInfoB_spec]

  have hAindep : ∀ i a b₁ b₂, respA i a b₁ = respA i a b₂ := hMIN.1
  have hBindep : ∀ i b a₁ a₂, respB i b a₁ = respB i b a₂ := hMIN.2

  have hTwinX :
      respB iBx f.x f = OutcomeA.x (respA iA f f.x) := by
    have hEq : chooseB iBx = (chooseA iA).x := by
      simp [hiA, hiBx]
    have hRaw := (hTwinRaw iA iBx).1 hEq
    simpa [hiA, hiBx] using hRaw

  have hTwinY :
      respB iBy f.y f = OutcomeA.y (respA iA f f.y) := by
    have hEq : chooseB iBy = (chooseA iA).y := by
      simp [hiA, hiBy]
    have hRaw := (hTwinRaw iA iBy).2.1 hEq
    simpa [hiA, hiBy] using hRaw

  have hTwinZ :
      respB iBz f.z f = OutcomeA.z (respA iA f f.z) := by
    have hEq : chooseB iBz = (chooseA iA).z := by
      simp [hiA, hiBz]
    have hRaw := (hTwinRaw iA iBz).2.2 hEq
    simpa [hiA, hiBz] using hRaw

  refine ⟨?_, ?_, ?_⟩
  · calc
      detRespB chooseB hFreeB respB f.x
          = respB iBx f.x (default : PeresFrame) := by
              simp [detRespB, iBx]
      _ = respB iBx f.x f := hBindep iBx f.x (default : PeresFrame) f
      _ = OutcomeA.x (respA iA f f.x) := hTwinX
      _ = OutcomeA.x (detRespA chooseA hFreeA respA f) := by
            simp [detRespA, iA]
  · have hAY : respA iA f f.y = respA iA f f.x := hAindep iA f f.y f.x
    calc
      detRespB chooseB hFreeB respB f.y
          = respB iBy f.y (default : PeresFrame) := by
              simp [detRespB, iBy]
      _ = respB iBy f.y f := hBindep iBy f.y (default : PeresFrame) f
      _ = OutcomeA.y (respA iA f f.y) := hTwinY
      _ = OutcomeA.y (respA iA f f.x) := by rw [hAY]
      _ = OutcomeA.y (detRespA chooseA hFreeA respA f) := by
            simp [detRespA, iA]
  · have hAZ : respA iA f f.z = respA iA f f.x := hAindep iA f f.z f.x
    calc
      detRespB chooseB hFreeB respB f.z
          = respB iBz f.z (default : PeresFrame) := by
              simp [detRespB, iBz]
      _ = respB iBz f.z f := hBindep iBz f.z (default : PeresFrame) f
      _ = OutcomeA.z (respA iA f f.z) := hTwinZ
      _ = OutcomeA.z (respA iA f f.x) := by rw [hAZ]
      _ = OutcomeA.z (detRespA chooseA hFreeA respA f) := by
            simp [detRespA, iA]

/--
Operational endpoint:
from free choices + MIN + raw SPIN/TWIN, extract deterministic responses and
derive the Kochen-Specker contradiction.
-/
theorem free_will_core
    {InfoA InfoB : Type*}
    (chooseA : InfoA → PeresFrame)
    (chooseB : InfoB → Dir)
    (hFreeA : FreeChoiceA chooseA)
    (hFreeB : FreeChoiceB chooseB)
    (respA : InfoA → PeresFrame → Dir → OutcomeA)
    (respB : InfoB → Dir → PeresFrame → Bool)
    (hMIN : MIN respA respB)
    (hSpinRaw : SpinAxiomRaw chooseA respA)
    (hTwinRaw : TwinAxiomRaw chooseA chooseB respA respB) :
    False := by
  let respA' := detRespA chooseA hFreeA respA
  let respB' := detRespB chooseB hFreeB respB
  have hSpin : SpinAxiom respA' := detRespA_spin chooseA hFreeA respA hSpinRaw
  have hTwin : TwinAxiom respA' respB' :=
    detResp_twin chooseA chooseB hFreeA hFreeB respA respB hMIN hTwinRaw
  exact no_deterministic_model respA' respB' hSpin hTwin

/--
Locality-driven endpoint:
derive `MIN` from accessibility/locality assumptions, then reuse
`free_will_core`.
-/
theorem free_will_core_from_locality
    {InfoA InfoB FactA FactB : Type*}
    (chooseA : InfoA → PeresFrame)
    (chooseB : InfoB → Dir)
    (hFreeA : FreeChoiceA chooseA)
    (hFreeB : FreeChoiceB chooseB)
    (respA : InfoA → PeresFrame → Dir → OutcomeA)
    (respB : InfoB → Dir → PeresFrame → Bool)
    (IA : AccessibleInfo (AEvent InfoA PeresFrame Dir) FactA)
    (IB : AccessibleInfo (BEvent InfoB Dir PeresFrame) FactB)
    (hLocA : LocalityA IA respA)
    (hLocB : LocalityB IB respB)
    (hNoSigA : RemoteChoiceInvisibleA IA)
    (hNoSigB : RemoteChoiceInvisibleB IB)
    (hSpinRaw : SpinAxiomRaw chooseA respA)
    (hTwinRaw : TwinAxiomRaw chooseA chooseB respA respB) :
    False := by
  have hMIN : MIN respA respB :=
    min_of_spacelike_locality IA IB respA respB hLocA hLocB hNoSigA hNoSigB
  exact free_will_core chooseA chooseB hFreeA hFreeB respA respB hMIN hSpinRaw hTwinRaw

/--
Factoring-driven endpoint:
derive `MIN` from locality plus local-fact factorization, then reuse
`free_will_core`.
-/
theorem free_will_core_from_factoring
    {InfoA InfoB FactA FactB : Type*}
    (chooseA : InfoA → PeresFrame)
    (chooseB : InfoB → Dir)
    (hFreeA : FreeChoiceA chooseA)
    (hFreeB : FreeChoiceB chooseB)
    (respA : InfoA → PeresFrame → Dir → OutcomeA)
    (respB : InfoB → Dir → PeresFrame → Bool)
    (IA : AccessibleInfo (AEvent InfoA PeresFrame Dir) FactA)
    (IB : AccessibleInfo (BEvent InfoB Dir PeresFrame) FactB)
    (hLocA : LocalityA IA respA)
    (hLocB : LocalityB IB respB)
    (hFactA : FactorsA IA)
    (hFactB : FactorsB IB)
    (hSpinRaw : SpinAxiomRaw chooseA respA)
    (hTwinRaw : TwinAxiomRaw chooseA chooseB respA respB) :
    False := by
  have hMIN : MIN respA respB :=
    min_of_locality_and_factoring IA IB respA respB hLocA hLocB hFactA hFactB
  exact free_will_core chooseA chooseB hFreeA hFreeB respA respB hMIN hSpinRaw hTwinRaw

/--
Bridge theorem using explicit locality/accessibility assumptions:
if predictability implies a free-choice/locality/SPIN/TWIN model,
then predictability is impossible.
-/
theorem not_predictable_of_free_will_locality
    {World Past Outcome InfoA InfoB FactA FactB : Type*}
    (past : World → Past)
    (out : World → Outcome)
    (hBridge :
      Predictable past out →
      ∃ (chooseA : InfoA → PeresFrame) (chooseB : InfoB → Dir)
        (respA : InfoA → PeresFrame → Dir → OutcomeA)
        (respB : InfoB → Dir → PeresFrame → Bool)
        (IA : AccessibleInfo (AEvent InfoA PeresFrame Dir) FactA)
        (IB : AccessibleInfo (BEvent InfoB Dir PeresFrame) FactB),
        FreeChoiceA chooseA ∧
        FreeChoiceB chooseB ∧
        LocalityA IA respA ∧
        LocalityB IB respB ∧
        RemoteChoiceInvisibleA IA ∧
        RemoteChoiceInvisibleB IB ∧
        SpinAxiomRaw chooseA respA ∧
        TwinAxiomRaw chooseA chooseB respA respB) :
    ¬ Predictable past out := by
  intro hPred
  rcases hBridge hPred with
    ⟨chooseA, chooseB, respA, respB, IA, IB, hFreeA, hFreeB, hLocA, hLocB, hNoSigA, hNoSigB, hSpin, hTwin⟩
  exact free_will_core_from_locality chooseA chooseB hFreeA hFreeB respA respB IA IB hLocA hLocB hNoSigA hNoSigB hSpin hTwin

/--
Unmarked-future endpoint from the locality-aware bridge.
-/
theorem unmarked_future_locality
    {World Past Outcome InfoA InfoB FactA FactB : Type*}
    (past : World → Past)
    (out : World → Outcome)
    (hBridge :
      Predictable past out →
      ∃ (chooseA : InfoA → PeresFrame) (chooseB : InfoB → Dir)
        (respA : InfoA → PeresFrame → Dir → OutcomeA)
        (respB : InfoB → Dir → PeresFrame → Bool)
        (IA : AccessibleInfo (AEvent InfoA PeresFrame Dir) FactA)
        (IB : AccessibleInfo (BEvent InfoB Dir PeresFrame) FactB),
        FreeChoiceA chooseA ∧
        FreeChoiceB chooseB ∧
        LocalityA IA respA ∧
        LocalityB IB respB ∧
        RemoteChoiceInvisibleA IA ∧
        RemoteChoiceInvisibleB IB ∧
        SpinAxiomRaw chooseA respA ∧
        TwinAxiomRaw chooseA chooseB respA respB) :
    UnmarkedFuture past out := by
  exact unmarkedFuture_of_not_predictable past out
    (not_predictable_of_free_will_locality past out hBridge)

/--
Accessibility-indexed locality endpoint:
if predictability would force a free-choice/locality/SPIN/TWIN model, then two
events with the same accessible information must disagree on outcome.
-/
theorem unmarked_future_accessible_locality
    {World Fact Past Outcome InfoA InfoB FactA FactB : Type*}
    (I : AccessibleInfo World Fact)
    (past : World → Past)
    (out : World → Outcome)
    (hCompat : ∀ w₁ w₂, SameAccessibleInfo I w₁ w₂ ↔ past w₁ = past w₂)
    (hBridge :
      Predictable past out →
      ∃ (chooseA : InfoA → PeresFrame) (chooseB : InfoB → Dir)
        (respA : InfoA → PeresFrame → Dir → OutcomeA)
        (respB : InfoB → Dir → PeresFrame → Bool)
        (IA : AccessibleInfo (AEvent InfoA PeresFrame Dir) FactA)
        (IB : AccessibleInfo (BEvent InfoB Dir PeresFrame) FactB),
        FreeChoiceA chooseA ∧
        FreeChoiceB chooseB ∧
        LocalityA IA respA ∧
        LocalityB IB respB ∧
        RemoteChoiceInvisibleA IA ∧
        RemoteChoiceInvisibleB IB ∧
        SpinAxiomRaw chooseA respA ∧
        TwinAxiomRaw chooseA chooseB respA respB) :
    UnmarkedFutureAccessible I out := by
  have hNotPred : ¬ Predictable past out :=
    not_predictable_of_free_will_locality past out hBridge
  exact unmarkedFuture_accessible_of_not_predictable I past out hCompat hNotPred

/--
Bridge theorem: if predictability would induce an operational model satisfying
Free-Will premises, then predictability is impossible.
-/
theorem not_predictable_of_free_will
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
    ¬ Predictable past out := by
  intro hPred
  rcases hBridge hPred with
    ⟨chooseA, chooseB, respA, respB, hFreeA, hFreeB, hMIN, hSpin, hTwin⟩
  exact free_will_core chooseA chooseB hFreeA hFreeB respA respB hMIN hSpin hTwin

/--
Free-Will endpoint in "unmarked future" form:
if predictability entails a SPIN/TWIN/MIN/free-choice operational model,
then two equal-past worlds must differ on outcome.
-/
theorem unmarked_future
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
  exact unmarkedFuture_of_not_predictable past out
    (not_predictable_of_free_will past out hBridge)

end HeytingLean.Physics.FreeWill
