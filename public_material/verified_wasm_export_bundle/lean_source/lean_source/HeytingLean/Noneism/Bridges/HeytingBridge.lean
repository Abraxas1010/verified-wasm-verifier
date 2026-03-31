import HeytingLean.Noneism.Bridges.LoFPrimordial

namespace HeytingLean
namespace Noneism
namespace Bridge

open Foundation
open Bridge.LoFPrimordial

/-!
Concrete Noneism -> LoF bridge built on `Bridge.LoFPrimordial`.

This replaces the previous placeholder shadow:
- `shadow p` picks `process` vs `counterProcess` in the two-point re-entry core,
- `omegaPull` maps that fixed-point back to predicates on `Nothing`,
- resulting predicates are exactly `Mark`/`Unmark`.
-/

noncomputable section

abbrev Omega : Type := LoFPrimordial.twoPointReentry.Omega

/-- Polarized shadow of a proposition into the two-point LoF core. -/
def shadow (p : Prop) : Omega := by
  classical
  exact if p then LoFPrimordial.twoPointReentry.process else LoFPrimordial.twoPointReentry.counterProcess

@[simp] theorem shadow_true : shadow True = LoFPrimordial.twoPointReentry.process := by
  simp [shadow]

@[simp] theorem shadow_false : shadow False = LoFPrimordial.twoPointReentry.counterProcess := by
  simp [shadow]

theorem process_ne_counter :
    LoFPrimordial.twoPointReentry.process ≠ LoFPrimordial.twoPointReentry.counterProcess := by
  exact LoFPrimordial.twoPoint_process_ne_counter

/-- `shadow` packaged into the polarized two-point core. -/
def shadowPolarized (p : Prop) : LoFPrimordial.Polarized := by
  classical
  by_cases hp : p
  · refine ⟨LoFPrimordial.twoPointReentry.process, Or.inl rfl⟩
  · refine ⟨LoFPrimordial.twoPointReentry.counterProcess, Or.inr rfl⟩

@[simp] theorem shadowPolarized_coe (p : Prop) :
    (shadowPolarized p).1 = shadow p := by
  classical
  by_cases hp : p <;> simp [shadowPolarized, shadow, hp]

@[simp] theorem shadowPolarized_toBool (p : Prop) [Decidable p] :
    LoFPrimordial.polarizedToBool (shadowPolarized p) = decide p := by
  by_cases hp : p <;> simp [shadowPolarized, hp]

theorem shadow_process_iff (p : Prop) :
    shadow p = LoFPrimordial.twoPointReentry.process ↔ p := by
  classical
  by_cases hp : p
  · simp [shadow, hp]
  · constructor
    · intro h
      have hcontra : LoFPrimordial.twoPointReentry.counterProcess =
          LoFPrimordial.twoPointReentry.process := by
        simpa [shadow, hp] using h
      exact False.elim (process_ne_counter hcontra.symm)
    · intro hp'
      exact False.elim (hp hp')

theorem shadow_counter_iff (p : Prop) :
    shadow p = LoFPrimordial.twoPointReentry.counterProcess ↔ ¬ p := by
  classical
  by_cases hp : p
  · constructor
    · intro hnp
      have hproc : LoFPrimordial.twoPointReentry.process =
          LoFPrimordial.twoPointReentry.counterProcess := by
        simpa [shadow, hp] using hnp
      exact False.elim (process_ne_counter hproc)
    · intro hnp
      exact False.elim (hnp hp)
  · simp [shadow, hp]

theorem omegaPull_shadow (p : Prop) [Decidable p] :
    LoFPrimordial.omegaPull (shadow p) =
      (if p then ({x | Mark x} : Set Noneism.Nothing) else {x | Unmark x}) := by
  by_cases hp : p <;> simp [shadow, hp, LoFPrimordial.omegaPull_process_eq_mark,
    LoFPrimordial.omegaPull_counterProcess_eq_unmark]

theorem omegaPull_shadow_mark_iff (p : Prop) :
    LoFPrimordial.omegaPull (shadow p) = ({x | Mark x} : Set Noneism.Nothing) ↔ p := by
  classical
  by_cases hp : p
  · simp [shadow, hp, LoFPrimordial.omegaPull_process_eq_mark]
  · constructor
    · intro hEq
      have hcontra :
          ({x | Unmark x} : Set Noneism.Nothing) = ({x | Mark x} : Set Noneism.Nothing) := by
        simpa [shadow, hp, LoFPrimordial.omegaPull_counterProcess_eq_unmark] using hEq
      have hCase : Mark seed ∨ Unmark seed := mark_or_unmark seed
      cases hCase with
      | inl hMark =>
          have hUnmark : Unmark seed := by
            change seed ∈ ({x | Unmark x} : Set Noneism.Nothing)
            rw [hcontra]
            exact hMark
          exact False.elim (PrimordialTension.mark_and_unmark_false (Nothing := Nothing) seed
            ⟨hMark, hUnmark⟩)
      | inr hUnmark =>
          have hMark : Mark seed := by
            change seed ∈ ({x | Mark x} : Set Noneism.Nothing)
            rw [← hcontra]
            exact hUnmark
          exact False.elim (PrimordialTension.mark_and_unmark_false (Nothing := Nothing) seed
            ⟨hMark, hUnmark⟩)
    · intro hp'
      exact False.elim (hp hp')

theorem omegaPull_shadow_unmark_iff (p : Prop) :
    LoFPrimordial.omegaPull (shadow p) = ({x | Unmark x} : Set Noneism.Nothing) ↔ ¬ p := by
  classical
  by_cases hp : p
  · constructor
    · intro hEq
      have hcontra :
          ({x | Mark x} : Set Noneism.Nothing) = ({x | Unmark x} : Set Noneism.Nothing) := by
        simpa [shadow, hp, LoFPrimordial.omegaPull_process_eq_mark] using hEq
      have hCase : Mark seed ∨ Unmark seed := mark_or_unmark seed
      cases hCase with
      | inl hMark =>
          have hUnmark : Unmark seed := by
            change seed ∈ ({x | Unmark x} : Set Noneism.Nothing)
            rw [← hcontra]
            exact hMark
          exact False.elim (PrimordialTension.mark_and_unmark_false (Nothing := Nothing) seed
            ⟨hMark, hUnmark⟩)
      | inr hUnmark =>
          have hMark : Mark seed := by
            change seed ∈ ({x | Mark x} : Set Noneism.Nothing)
            rw [hcontra]
            exact hUnmark
          exact False.elim (PrimordialTension.mark_and_unmark_false (Nothing := Nothing) seed
            ⟨hMark, hUnmark⟩)
    · intro hnp
      exact False.elim (hnp hp)
  · simp [shadow, hp, LoFPrimordial.omegaPull_counterProcess_eq_unmark]

end

end Bridge
end Noneism
end HeytingLean
