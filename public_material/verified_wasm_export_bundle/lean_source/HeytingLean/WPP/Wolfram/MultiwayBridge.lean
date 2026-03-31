import HeytingLean.WPP.Wolfram.ConfluenceTheory
import HeytingLean.WPP.Wolfram.Multiway

/-!
# Wolfram ⇄ WPP.Multiway bridge

This file relates the Wolfram rewrite semantics (`System.Step` from the relation-theoretic
layer) to the **finite** `Finset`-based multiway enumerator (`System.stepStates`) and the
generic `WppRule` interface.

In particular, for finite `P` and `V`:

* membership `t ∈ sys.stepStates s` is equivalent to the one-step relation `sys.Step s t`,
* the resulting `WppRule.StepStar` coincides with `Relation.ReflTransGen sys.Step`.
-/

namespace HeytingLean
namespace WPP
namespace Wolfram

namespace System

universe u v

variable {V : Type u} {P : Type v} (sys : System V P)

section Finite

variable [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

/-- One-step Wolfram `Step` is exactly the `Finset` successor membership from `stepStates`. -/
theorem stepStates_iff_step {s t : HGraph V} :
    t ∈ sys.stepStates s ↔ Step (sys := sys) s t := by
  constructor
  · intro ht
    rcases (sys.mem_stepStates_iff (P := P) (V := V) (s := s) (t := t)).1 ht with
      ⟨ed, hedAll, hedApp, hEq⟩
    let e : sys.Event := { idx := ed.1, σ := ed.2 }
    refine ⟨e, ?_, ?_⟩
    · simpa [EventData.Applicable, Event.Applicable, Event.input, e] using hedApp
    · simpa [EventData.apply, Event.apply, Event.input, Event.output, e] using hEq
  · rintro ⟨e, happ, hEq⟩
    set ed : sys.EventData := (e.idx, e.σ) with hed
    have hedAll : ed ∈ sys.allEventData := by
      have : ed.2 ∈ allSubsts (P := P) (V := V) :=
        mem_allSubsts (P := P) (V := V) ed.2
      exact (sys.mem_allEventData_iff (P := P) (V := V) (ed := ed)).2 this
    have hedApp : EventData.Applicable (sys := sys) ed s := by
      simpa [hed, EventData.Applicable, Event.Applicable, Event.input] using happ
    have hedEq : EventData.apply (sys := sys) ed s = t := by
      simpa [hed, EventData.apply, Event.apply, Event.input, Event.output] using hEq
    exact (sys.mem_stepStates_iff (P := P) (V := V) (s := s) (t := t)).2 ⟨ed, hedAll, hedApp, hedEq⟩

/-- `WppRule.StepStar` for the finite `toWppRule` coincides with `System.StepStar`. -/
theorem wpp_stepStar_iff_stepStar {s t : HGraph V} :
    WppRule.StepStar (R := sys.toWppRule) s t ↔ StepStar (sys := sys) s t := by
  constructor
  · intro h
    induction h with
    | refl s =>
        exact Relation.ReflTransGen.refl
    | tail hst htu ih =>
        have hab : Step (sys := sys) _ _ :=
          (stepStates_iff_step (sys := sys) (s := _) (t := _)).1 (by
            simpa [System.toWppRule, WppRule.stepRel] using hst)
        exact Relation.ReflTransGen.head (r := Step (sys := sys)) hab ih
  · intro h
    induction h with
    | refl =>
        exact WppRule.StepStar.refl _
    | tail hab hstep ih =>
        -- We have a chain to an intermediate state, then a final one-step `Step`.
        rename_i b c
        have hrel : WppRule.stepRel (sys.toWppRule) b c := by
          have : c ∈ sys.stepStates b :=
            (stepStates_iff_step (sys := sys) (s := b) (t := c)).2 hstep
          simpa [System.toWppRule, WppRule.stepRel] using this
        have hbc : WppRule.StepStar (R := sys.toWppRule) b c :=
          WppRule.StepStar.tail hrel (WppRule.StepStar.refl c)
        exact WppRule.StepStar.trans (R := sys.toWppRule) ih hbc

end Finite

end System

end Wolfram
end WPP
end HeytingLean
