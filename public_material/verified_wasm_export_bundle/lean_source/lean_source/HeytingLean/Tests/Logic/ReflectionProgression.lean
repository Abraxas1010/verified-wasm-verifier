import HeytingLean.Logic.ReflectionProgression
import Mathlib.SetTheory.Ordinal.Arithmetic

namespace HeytingLean.Tests.Logic

open HeytingLean.Logic
open scoped Classical
open Ordinal
open Order

noncomputable section

/-- Simple successor law that collapses every stage to the top nucleus on `Prop`. -/
def collapseLaw : ReflectionLaw (α := Prop) where
  step _ := ⊤
  step_mono _ _ _ := le_top
  le_step _ := le_top

/-- The corresponding seed starts from the identity nucleus. -/
def collapseSeed : ReflectionSeed (α := Prop) where
  base := ⊥
  law := collapseLaw

@[simp] lemma progression_zero : collapseSeed.progression 0 = (⊥ : Nucleus Prop) := by
  simpa [collapseSeed]
    using ReflectionSeed.progression_zero (seed := collapseSeed)

@[simp] lemma progression_one : collapseSeed.progression 1 = (⊤ : Nucleus Prop) := by
  simpa [collapseSeed, collapseLaw]
    using ReflectionSeed.progression_succ (seed := collapseSeed) 0

lemma monotone_example :
    collapseSeed.progression 0 ≤ collapseSeed.progression (Order.succ 1) := by
  have h₀₁ : collapseSeed.progression 0 ≤ collapseSeed.progression 1 := by
    simpa using (ReflectionSeed.progression_monotone (seed := collapseSeed)) bot_le
  have h₁succ := ReflectionSeed.le_progression_succ (seed := collapseSeed) 1
  exact h₀₁.trans h₁succ

/-- Uniform reflection law instantiation on `Prop` using Γ = {False}. -/
def uniformLawFalse : ReflectionLaw (α := Prop) :=
  ReflectionLaw.uniform (α := Prop) ({False} : Finset Prop)

lemma uniform_law_fixes_schema :
    succStepUniform (α := Prop) (⊤ : Nucleus Prop) ({False} : Finset Prop)
      ((⊤ : Nucleus Prop) False ⇨ False) = True := by
  have hmem : False ∈ ({False} : Finset Prop) := by simp
  simpa using
    succStepUniform_law_true (Rα := (⊤ : Nucleus Prop)) (Γ := ({False} : Finset Prop))
      (p := False) hmem

lemma uniform_law_inflation :
    (⊥ : Nucleus Prop) ≤
      succStepUniform (α := Prop) (⊥ : Nucleus Prop) ({False} : Finset Prop) :=
  le_succStepUniform (Rα := (⊥ : Nucleus Prop)) (Γ := ({False} : Finset Prop))

end
