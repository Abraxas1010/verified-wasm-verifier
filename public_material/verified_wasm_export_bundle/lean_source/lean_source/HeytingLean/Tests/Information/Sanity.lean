import HeytingLean.Information.Trace
import HeytingLean.LoF.Instances

namespace HeytingLean
namespace Tests
namespace Information

open scoped Classical

open Set
open HeytingLean.LoF
open HeytingLean.Information

/-!
Sanity checks for the “information as distinction” stack.

These are compile-time tests: we build a small `Reentry` instance and show that

1. the fuel-bounded runner finds the stable support point, and
2. the proof-trace size matches the step count.
-/

def setTrue : Set Bool := {b | b = true}
def setFalse : Set Bool := {b | b = false}

noncomputable def reentryBool : Reentry (Set Bool) := by
  classical
  refine
    { nucleus := (⊥ : Nucleus (Set Bool))
      primordial := setTrue
      counter := setFalse
      support := setTrue
      primordial_mem := rfl
      counter_mem := rfl
      primordial_nonbot := by
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have hmem : (true : Bool) ∈ setTrue := by simp [setTrue]
        simp [h] at hmem
      counter_nonbot := by
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have hmem : (false : Bool) ∈ setFalse := by simp [setFalse]
        simp [h] at hmem
      orthogonal := by
        ext b
        cases b <;> simp [setTrue, setFalse, inf_eq_inter]
      primordial_in_support := le_rfl
      map_bot := by
        simp
      primordial_minimal := by
        intro x _hx_fix hx_pos hx_sup
        have hx_ne : x ≠ (⊥ : Set Bool) := bot_lt_iff_ne_bot.mp hx_pos
        have hx_nonempty : x.Nonempty :=
          Set.nonempty_iff_ne_empty.mpr (by simpa using hx_ne)
        obtain ⟨w, hw⟩ := hx_nonempty
        have hw_true : w = true := by
          have := hx_sup hw
          simpa [setTrue] using this
        have hx_true : true ∈ x := by simpa [hw_true] using hw
        intro b hb
        have hb_true : b = true := by simpa [setTrue] using hb
        subst hb_true
        simpa using hx_true }

def interpret : InfoState → Set Bool
  | .primordial => setTrue
  | .counter => setFalse

@[simp] lemma interpret_primordial : interpret InfoState.primordial = setTrue := rfl
@[simp] lemma interpret_counter : interpret InfoState.counter = setFalse := rfl

lemma stable_setTrue : IsStable reentryBool setTrue := by
  refine ⟨reentryBool.primordial_mem, ?_⟩
  exact ⟨reentryBool.primordial_nonbot, le_rfl⟩

lemma not_stable_setFalse : ¬ IsStable reentryBool setFalse := by
  intro h
  have hle : setFalse ≤ reentryBool.support := h.2.2
  have : (false : Bool) ∈ setTrue := hle (by simp [setFalse])
  simp [setTrue] at this

@[simp] lemma runUntilStable?_primordial :
    runUntilStable? reentryBool interpret 2 InfoState.primordial = some (0, setTrue) := by
  classical
  simp [runUntilStable?, stable_setTrue]

example :
    runUntilStable? reentryBool interpret 3 InfoState.counter =
      some (1, setTrue) := by
  classical
  simp [runUntilStable?, not_stable_setFalse, stable_setTrue]

example :
    (runUntilStable reentryBool interpret 3 InfoState.counter).1 = 1 := by
  classical
  have hRun : runUntilStable? reentryBool interpret 3 InfoState.counter = some (1, setTrue) := by
    simp [runUntilStable?, not_stable_setFalse, stable_setTrue]
  simp [runUntilStable, hRun]

def expectedCertified : RunResult reentryBool interpret InfoState.counter :=
  { steps := 1
    final := setTrue
    cert :=
      ReachesFixedPoint.step (R := reentryBool) (interpret := interpret) InfoState.counter
        not_stable_setFalse
        (ReachesFixedPoint.stable (R := reentryBool) (interpret := interpret) InfoState.primordial
          stable_setTrue) }

example :
    ∃ r, runUntilStableCertified? reentryBool interpret 3 InfoState.counter = some r
      ∧ r.steps = 1
      ∧ r.final = setTrue
      ∧ ReachesFixedPoint.structuralInformation r.cert = 1 := by
  classical
  refine ⟨expectedCertified, ?_⟩
  refine And.intro ?_ (And.intro rfl (And.intro rfl ?_))
  · simp [expectedCertified, runUntilStableCertified?, interpret, not_stable_setFalse, stable_setTrue]
  · simp [expectedCertified, ReachesFixedPoint.structuralInformation]

example :
    ∀ {a n} (p : ReachesFixedPoint reentryBool interpret InfoState.counter a n),
      ReachesFixedPoint.structuralInformation p = n := by
  intro a n p
  simpa using ReachesFixedPoint.information_is_dynamics (p := p)

-- Stage 1 bridge compiles: `Bool ≃ Set Unit`.
example : (boolEquivSetUnit : Bool ≃ Set Unit).toFun true = ({()} : Set Unit) := by
  ext u
  cases u
  simp [boolEquivSetUnit, boolToSetUnit]

end Information
end Tests
end HeytingLean
