import HeytingLean.Physics.FreeWill
import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerSphere
import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerSphereLocal

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

#check no101_peres33
#check no_deterministic_model
#check free_will_core
#check free_will_core_from_locality
#check unmarked_future
#check unmarked_future_locality
#check unmarked_future_accessible_locality
#check unmarked_future_internal
#check unmarked_future_via_internal
#check min_of_spacelike_locality
#check min_of_locality_and_factoring
#check factorsA_implies_remoteInvisibleA
#check factorsB_implies_remoteInvisibleB
#check free_will_core_from_factoring
#check unmarkedFuture_accessible_of_projection
#check no_global_lof_marking
#check no_global_marking_for_peres
#check HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerSphere.ksScenario_contextual
#check HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerSphereLocal.ksScenarioLocal_contextual

example
    {InfoA InfoB : Type*}
    (chooseA : InfoA → PeresFrame)
    (chooseB : InfoB → Dir)
    (respA : InfoA → PeresFrame → Dir → OutcomeA)
    (respB : InfoB → Dir → PeresFrame → Bool)
    (hFreeA : FreeChoiceA chooseA)
    (hFreeB : FreeChoiceB chooseB)
    (hMIN : MIN respA respB)
    (hSpin : SpinAxiomRaw chooseA respA)
    (hTwin : TwinAxiomRaw chooseA chooseB respA respB) :
    False := by
  exact free_will_core chooseA chooseB hFreeA hFreeB respA respB hMIN hSpin hTwin

example
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
  exact unmarked_future past out hBridge

section AssumptionSensitivity

abbrev IAEvent := AEvent Unit Bool Bool
abbrev IBEvent := BEvent Unit Bool Bool

def fullInfoA : AccessibleInfo IAEvent IAEvent where
  facts e := {e}

def fullInfoB : AccessibleInfo IBEvent IBEvent where
  facts e := {e}

def respASignal : Unit → Bool → Bool → Bool := fun _ _ b => b
def respBSignal : Unit → Bool → Bool → Bool := fun _ _ a => a
def respAConst : Unit → Bool → Bool → Bool := fun _ _ _ => true
def respBConst : Unit → Bool → Bool → Bool := fun _ _ _ => false

def factoredInfoA : AccessibleInfo IAEvent (Unit × Bool) where
  facts e := {((Prod.fst e), (Prod.fst (Prod.snd e)))}

def factoredInfoB : AccessibleInfo IBEvent (Unit × Bool) where
  facts e := {((Prod.fst e), (Prod.fst (Prod.snd e)))}

example : LocalityA fullInfoA respASignal := by
  intro i a b₁ b₂ hSame
  dsimp [SameAccessibleInfo, fullInfoA] at hSame
  have hb : b₁ = b₂ := by
    have hPair : (i, a, b₁) = (i, a, b₂) := Set.singleton_injective hSame
    exact congrArg Prod.snd (congrArg Prod.snd hPair)
  simp [respASignal, hb]

example : LocalityB fullInfoB respBSignal := by
  intro i b a₁ a₂ hSame
  dsimp [SameAccessibleInfo, fullInfoB] at hSame
  have ha : a₁ = a₂ := by
    have hPair : (i, b, a₁) = (i, b, a₂) := Set.singleton_injective hSame
    exact congrArg Prod.snd (congrArg Prod.snd hPair)
  simp [respBSignal, ha]

example : ¬ RemoteChoiceInvisibleA fullInfoA := by
  intro hNoSig
  have hEq := hNoSig () false false true
  have hPair : (((), false, false) : IAEvent) = ((), false, true) := Set.singleton_injective hEq
  have hb : false = true := congrArg Prod.snd (congrArg Prod.snd hPair)
  exact Bool.false_ne_true hb

example : ¬ RemoteChoiceInvisibleB fullInfoB := by
  intro hNoSig
  have hEq := hNoSig () false false true
  have hPair : (((), false, false) : IBEvent) = ((), false, true) := Set.singleton_injective hEq
  have ha : false = true := congrArg Prod.snd (congrArg Prod.snd hPair)
  exact Bool.false_ne_true ha

example : ¬ (∀ i a b₁ b₂, respASignal i a b₁ = respASignal i a b₂) := by
  intro hConst
  have hEq : respASignal () false false = respASignal () false true := by
    simpa using hConst () false false true
  exact Bool.false_ne_true hEq

example : ¬ (∀ i b a₁ a₂, respBSignal i b a₁ = respBSignal i b a₂) := by
  intro hConst
  have hEq : respBSignal () true false = respBSignal () true true := by
    simpa using hConst () true false true
  exact Bool.false_ne_true hEq

example : FactorsA factoredInfoA := by
  refine ⟨fun i a => {(i, a)}, ?_⟩
  intro i a b
  simp [factoredInfoA]

example : FactorsB factoredInfoB := by
  refine ⟨fun i b => {(i, b)}, ?_⟩
  intro i b a
  simp [factoredInfoB]

example : RemoteChoiceInvisibleA factoredInfoA := by
  apply factorsA_implies_remoteInvisibleA factoredInfoA
  refine ⟨fun i a => {(i, a)}, ?_⟩
  intro i a b
  simp [factoredInfoA]

example : RemoteChoiceInvisibleB factoredInfoB := by
  apply factorsB_implies_remoteInvisibleB factoredInfoB
  refine ⟨fun i b => {(i, b)}, ?_⟩
  intro i b a
  simp [factoredInfoB]

example : LocalityA factoredInfoA respAConst := by
  intro i a b₁ b₂ _hSame
  simp [respAConst]

example : LocalityB factoredInfoB respBConst := by
  intro i b a₁ a₂ _hSame
  simp [respBConst]

example : MIN respAConst respBConst := by
  exact min_of_locality_and_factoring factoredInfoA factoredInfoB
    respAConst respBConst
    (by
      intro i a b₁ b₂ _hSame
      simp [respAConst])
    (by
      intro i b a₁ a₂ _hSame
      simp [respBConst])
    (by
      refine ⟨fun i a => {(i, a)}, ?_⟩
      intro i a b
      simp [factoredInfoA])
    (by
      refine ⟨fun i b => {(i, b)}, ?_⟩
      intro i b a
      simp [factoredInfoB])

end AssumptionSensitivity

end HeytingLean.Physics.FreeWill
