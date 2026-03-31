import Mathlib.Logic.Basic
import HeytingLean.Constructor.Core
import HeytingLean.Crypto.ConstructiveHardness.ContextualityPhysical

/-!
# Constructive Hardness: contextuality ⇒ impossibility (skeleton)

This module is intended to be *extractable* as a small, standalone slice.
It depends only on:
* the existing CryptoSheaf/Quantum `EmpiricalModel` layer (global sections); and
* the generic nucleus-based modality scaffold in `HeytingLean.Constructor.Core`.

This file is the **optional** “nucleus-lift” add-on.

Why it exists:
- Mathlib’s `Nucleus` is inflationary (`P → R P`), which is *not* the CT polarity.
- However, some parts of this codebase already use `Nucleus` as a general modality scaffold.
  If you interpret a particular `R : Nucleus Prop` as a “possibility” predicate for a specific `P`
  and can prove **soundness** (`R P → P`), then `¬P` implies `Constructor.impossible R P`.

For the CT-polarty-first slice intended for extraction, see
`HeytingLean.Crypto.ConstructiveHardness.ContextualityPhysical`.
-/

namespace HeytingLean
namespace Crypto
namespace ConstructiveHardness

open HeytingLean.Constructor
open HeytingLean.LoF.CryptoSheaf.Quantum

/-!
## Lifting `¬P` to “impossible under a modality”

For `Prop`, a nucleus `R : Nucleus Prop` acts like a *modality*.
`Constructor.impossible R P` is definitionally `R P = False`.

To derive `R P = False` from `¬P`, we need **soundness** for the specific proposition:
`R P → P`. This is exactly the shape we expect when `R P` means “P is physically possible /
constructible / realisable” (or “a constructor for P exists”): from such a witness, `P` follows.
-/

theorem impossible_of_not_of_sound
    (R : Nucleus Prop) {P : Prop}
    (hSound : R P → P) :
    ¬ P → Constructor.impossible (R := R) P := by
  intro hNotP
  -- Show `R P = False` by propositional extensionality from `R P ↔ False`.
  apply propext
  constructor
  · intro hRP
    exact (hNotP (hSound hRP)).elim
  · intro hFalse
    exact False.elim hFalse

/-!
## Impossibility for the identity nucleus on `Prop`

Mathlib’s nucleus order has `⊥` as the identity nucleus. For `Prop`, this
means `Constructor.impossible (R := ⊥) P` is equivalent to `¬ P`.
-/

abbrev PropIdNucleus : Nucleus Prop := (⊥ : Nucleus Prop)

lemma impossible_propId_implies_not (P : Prop) :
    Constructor.impossible (R := PropIdNucleus) P → ¬ P := by
  intro hP h
  have hEq : P = False := by
    simpa [Constructor.impossible, PropIdNucleus] using hP
  cases hEq
  exact h

lemma impossible_propId_iff_not (P : Prop) :
    Constructor.impossible (R := PropIdNucleus) P ↔ ¬ P := by
  -- `PropIdNucleus` is the identity nucleus (`⊥` in `Nucleus Prop`).
  -- So `impossible` reduces to `P = False`.
  constructor
  · exact impossible_propId_implies_not (P := P)
  · intro hnot
    -- `P = False` by propositional extensionality from `P ↔ False`.
    have hEq : P = False := by
      apply propext
      constructor
      · intro hP
        exact (hnot hP).elim
      · intro hFalse
        exact False.elim hFalse
    simpa [Constructor.impossible, PropIdNucleus] using hEq

/-!
## Hardness scenario and bridge theorem (general)

We define “hardness scenario” for an empirical model as impossibility of the
global-section task under the identity nucleus on `Prop`.
-/

abbrev HardnessScenario
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) : Prop :=
  Constructor.impossible (R := PropIdNucleus)
    (GlobalSectionTask X cover e coverSubX)

theorem contextuality_implies_hardness
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    NoGlobalSection X cover e coverSubX →
      HardnessScenario X cover e coverSubX := by
  intro hNo
  -- The proof factors into:
  -- 1) a fully constructive core lemma (`NoGlobalSection` is a negation); and
  -- 2) a Prop-extensionality step converting `¬ P` into `P = False`, because
  --    `Constructor.impossible` is defined via equality-to-⊥.
  have hNot : ¬ GlobalSectionTask X cover e coverSubX :=
    contextuality_implies_not_globalSectionTask
      (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) hNo
  exact (impossible_propId_iff_not (P := GlobalSectionTask X cover e coverSubX)).2 hNot

/-!
## The non-tautological “physical” bridge shape (still abstract)

If you later instantiate a nucleus `R_phys : Nucleus Prop` expressing *physical realisability*
of the global-section task, and you can prove the soundness direction
`R_phys P → P`, then contextuality implies **physical impossibility** under that modality.

This is the point where constructor-theoretic content enters: it is *not* a tautology
because `R_phys` is not the identity nucleus and its soundness must be justified by a model.
-/

theorem contextuality_implies_impossible_of_soundNucleus
    (R : Nucleus Prop)
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X)
    (hSound : R (GlobalSectionTask X cover e coverSubX) →
              GlobalSectionTask X cover e coverSubX) :
    NoGlobalSection X cover e coverSubX →
      Constructor.impossible (R := R) (GlobalSectionTask X cover e coverSubX) := by
  intro hNo
  have hNot : ¬ GlobalSectionTask X cover e coverSubX :=
    contextuality_implies_not_globalSectionTask
      (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) hNo
  exact impossible_of_not_of_sound (R := R) (P := GlobalSectionTask X cover e coverSubX) hSound hNot

theorem hardness_iff_noGlobal
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    HardnessScenario X cover e coverSubX ↔
      NoGlobalSection X cover e coverSubX := by
  -- In the current “Prop + identity nucleus” encoding, hardness is exactly no-global-section.
  -- This is intentional: it cleanly separates the *obstruction criterion* from later
  -- refinements where the nucleus encodes physical/constructive realizability.
  constructor
  · intro hHard
    -- Convert `Constructor.impossible` back to `¬ HasGlobalSection`.
    have : ¬ GlobalSectionTask X cover e coverSubX :=
      (impossible_propId_iff_not (P := GlobalSectionTask X cover e coverSubX)).1 hHard
    simpa [GlobalSectionTask, NoGlobalSection, HasGlobalSection] using this
  · intro hNo
    exact contextuality_implies_hardness (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) hNo

end ConstructiveHardness
end Crypto
end HeytingLean
