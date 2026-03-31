import HeytingLean.LoF.Combinators.SKY

/-!
# LoFSKY — a concrete LoF⇄SKY term correspondence

This file formalizes a **minimal, honest** correspondence between a “LoF-combinator” syntax and the
existing SKY combinator syntax `HeytingLean.LoF.Comb`.

Key design choice (objectivity / bias control):

*We do not attempt to formalize the full Laws of Form calculus here.*
Instead, we define a term language whose primitive constants are:

- `mark`    (LoF “mark”)
- `unmark`  (LoF “unmark”)
- `reentry` (LoF “re-entry” / self-reference)

and whose only constructor is application. This matches the level at which the program spec claims:

> “LoF primitives (Mark/Unmark/Re-entry) are the three combinators K/S/Y under a different reading.”

We then make that identification precise by giving an explicit equivalence between these terms and
the SKY terms, plus step-preservation results for the corresponding rewrite relations.
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open HeytingLean.LoF

/-! ## LoF combinator terms -/

/-- A minimal “LoF combinator” term language: three primitive constants + application. -/
inductive LoFTerm where
  | mark
  | unmark
  | reentry
  | app (f a : LoFTerm)
deriving DecidableEq, Repr

namespace LoFTerm

open HeytingLean.LoF.Comb

/-- Swap the names `mark` and `unmark` (leaving `reentry` fixed). This packages the fact that the
program spec and this repo sometimes use opposite naming conventions for the same underlying
`K`/`S` primitives. -/
def swapMarkUnmark : LoFTerm → LoFTerm
  | .mark => .unmark
  | .unmark => .mark
  | .reentry => .reentry
  | .app f a => .app (swapMarkUnmark f) (swapMarkUnmark a)

@[simp] theorem swapMarkUnmark_mark : swapMarkUnmark .mark = .unmark := rfl
@[simp] theorem swapMarkUnmark_unmark : swapMarkUnmark .unmark = .mark := rfl
@[simp] theorem swapMarkUnmark_reentry : swapMarkUnmark .reentry = .reentry := rfl
@[simp] theorem swapMarkUnmark_app (f a : LoFTerm) :
    swapMarkUnmark (.app f a) = .app (swapMarkUnmark f) (swapMarkUnmark a) := rfl

@[simp] theorem swapMarkUnmark_swapMarkUnmark : ∀ t : LoFTerm, swapMarkUnmark (swapMarkUnmark t) = t := by
  intro t
  induction t with
  | mark => rfl
  | unmark => rfl
  | reentry => rfl
  | app f a ihf iha =>
      simp [swapMarkUnmark, ihf, iha]

/-- Interpretation of LoF primitive terms as SKY terms.

We choose the convention:
- `mark ↦ S`
- `unmark ↦ K`
- `reentry ↦ Y`

This matches `HeytingLean.LoF.Combinators.Heyting.combToLoF` (which maps `S ↦ mark`, `K ↦ unmark`,
`Y ↦ reentry`).

If you prefer the alternate convention “mark ↦ K, unmark ↦ S”, you can define a second interpretation
and re-run the same proofs: the development below is intentionally lightweight.
-/
def toSKY : LoFTerm → Comb
  | .mark => .S
  | .unmark => .K
  | .reentry => .Y
  | .app f a => .app (toSKY f) (toSKY a)

/-- Alternate interpretation matching the spec-table convention:

- `mark ↦ K`
- `unmark ↦ S`
- `reentry ↦ Y`

This is just `toSKY` after swapping the names `mark` and `unmark`. -/
def toSKY_spec (t : LoFTerm) : Comb :=
  toSKY (swapMarkUnmark t)

@[simp] theorem toSKY_spec_mark : toSKY_spec .mark = (.K : Comb) := rfl
@[simp] theorem toSKY_spec_unmark : toSKY_spec .unmark = (.S : Comb) := rfl
@[simp] theorem toSKY_spec_reentry : toSKY_spec .reentry = (.Y : Comb) := rfl
@[simp] theorem toSKY_spec_app (f a : LoFTerm) :
    toSKY_spec (.app f a) = .app (toSKY_spec f) (toSKY_spec a) := by
  simp [toSKY_spec, swapMarkUnmark, toSKY]

/-- Read a SKY term as an LoF term (structure-preserving renaming). -/
def ofSKY : Comb → LoFTerm
  | .S => .mark
  | .K => .unmark
  | .Y => .reentry
  | .app f a => .app (ofSKY f) (ofSKY a)

/-- The `ofSKY` map corresponding to `toSKY_spec` (spec-table naming). -/
def ofSKY_spec (t : Comb) : LoFTerm :=
  swapMarkUnmark (ofSKY t)

@[simp] theorem toSKY_ofSKY : ∀ t : Comb, toSKY (ofSKY t) = t := by
  intro t
  induction t with
  | K => rfl
  | S => rfl
  | Y => rfl
  | app f a ihf iha =>
      simp [ofSKY, toSKY, ihf, iha]

@[simp] theorem ofSKY_toSKY : ∀ t : LoFTerm, ofSKY (toSKY t) = t := by
  intro t
  induction t with
  | mark => rfl
  | unmark => rfl
  | reentry => rfl
  | app f a ihf iha =>
      simp [toSKY, ofSKY, ihf, iha]

@[simp] theorem toSKY_spec_ofSKY_spec : ∀ t : Comb, toSKY_spec (ofSKY_spec t) = t := by
  intro t
  simp [toSKY_spec, ofSKY_spec, swapMarkUnmark_swapMarkUnmark, toSKY_ofSKY]

@[simp] theorem ofSKY_spec_toSKY_spec : ∀ t : LoFTerm, ofSKY_spec (toSKY_spec t) = t := by
  intro t
  simp [toSKY_spec, ofSKY_spec, swapMarkUnmark_swapMarkUnmark, ofSKY_toSKY]

theorem ofSKY_leftInverse : Function.LeftInverse ofSKY toSKY := by
  intro t
  simp

theorem ofSKY_rightInverse : Function.RightInverse ofSKY toSKY := by
  intro t
  simp

theorem toSKY_injective : Function.Injective toSKY := by
  intro a b h
  have := congrArg ofSKY h
  simpa using this

theorem toSKY_surjective : Function.Surjective toSKY := by
  intro t
  refine ⟨ofSKY t, ?_⟩
  simp

theorem toSKY_spec_injective : Function.Injective toSKY_spec := by
  intro a b h
  have : toSKY (swapMarkUnmark a) = toSKY (swapMarkUnmark b) := by
    simpa [toSKY_spec] using h
  have hs : swapMarkUnmark a = swapMarkUnmark b := toSKY_injective this
  have := congrArg swapMarkUnmark hs
  simpa [swapMarkUnmark_swapMarkUnmark] using this

theorem toSKY_spec_surjective : Function.Surjective toSKY_spec := by
  intro t
  refine ⟨ofSKY_spec t, ?_⟩
  simp

abbrev Bijective {α β : Type} (f : α → β) : Prop :=
  Function.Injective f ∧ Function.Surjective f

theorem toSKY_bijective : Bijective toSKY :=
  ⟨toSKY_injective, toSKY_surjective⟩

theorem ofSKY_bijective : Bijective ofSKY := by
  refine ⟨?inj, ?surj⟩
  · intro a b h
    have := congrArg toSKY h
    simpa using this
  · intro t
    refine ⟨toSKY t, ?_⟩
    simp

theorem toSKY_spec_bijective : Bijective toSKY_spec :=
  ⟨toSKY_spec_injective, toSKY_spec_surjective⟩

end LoFTerm

/-! ## LoF rewriting (mirrors SKY rewriting under `LoFTerm.toSKY`) -/

namespace LoFStep

open LoFTerm

/-- One-step reduction rules on `LoFTerm`, obtained by renaming the SKY `K/S/Y` rules. -/
inductive Step : LoFTerm → LoFTerm → Prop where
  | unmark_rule (x y : LoFTerm) :
      Step (LoFTerm.app (LoFTerm.app .unmark x) y) x
  | mark_rule (x y z : LoFTerm) :
      Step (LoFTerm.app (LoFTerm.app (LoFTerm.app .mark x) y) z)
        (LoFTerm.app (LoFTerm.app x z) (LoFTerm.app y z))
  | reentry_rule (f : LoFTerm) :
      Step (LoFTerm.app .reentry f) (LoFTerm.app f (LoFTerm.app .reentry f))
  | app_left {f f' a} :
      Step f f' → Step (LoFTerm.app f a) (LoFTerm.app f' a)
  | app_right {f a a'} :
      Step a a' → Step (LoFTerm.app f a) (LoFTerm.app f a')

/-- Multi-step reachability on `LoFTerm` (reflexive-transitive closure). -/
inductive Steps : LoFTerm → LoFTerm → Prop where
  | refl (t : LoFTerm) : Steps t t
  | trans {t u v} : Step t u → Steps u v → Steps t v

namespace Steps

theorem transitive {t u v : LoFTerm} : Steps t u → Steps u v → Steps t v := by
  intro htu huv
  induction htu with
  | refl _ =>
      simpa using huv
  | trans hstep hsteps ih =>
      exact Steps.trans hstep (ih huv)

end Steps

open HeytingLean.LoF.Comb

/-- `LoFStep.Step` is preserved by the renaming `LoFTerm.toSKY`. -/
theorem step_toSKY {t u : LoFTerm} :
    Step t u → Comb.Step (LoFTerm.toSKY t) (LoFTerm.toSKY u) := by
  intro h
  induction h with
  | unmark_rule x y =>
      -- K-rule
      simpa [LoFTerm.toSKY] using Comb.Step.K_rule (x := LoFTerm.toSKY x) (y := LoFTerm.toSKY y)
  | mark_rule x y z =>
      -- S-rule
      simpa [LoFTerm.toSKY] using
        Comb.Step.S_rule (x := LoFTerm.toSKY x) (y := LoFTerm.toSKY y) (z := LoFTerm.toSKY z)
  | reentry_rule f =>
      -- Y-rule
      simpa [LoFTerm.toSKY] using Comb.Step.Y_rule (f := LoFTerm.toSKY f)
  | app_left h ih =>
      simpa [LoFTerm.toSKY] using Comb.Step.app_left (f := LoFTerm.toSKY _) (a := LoFTerm.toSKY _) ih
  | app_right h ih =>
      simpa [LoFTerm.toSKY] using Comb.Step.app_right (f := LoFTerm.toSKY _) (a := LoFTerm.toSKY _) ih

/-- Multi-step reachability is preserved by `LoFTerm.toSKY`. -/
theorem steps_toSKY {t u : LoFTerm} :
    Steps t u → Comb.Steps (LoFTerm.toSKY t) (LoFTerm.toSKY u) := by
  intro h
  induction h with
  | refl t =>
      exact Comb.Steps.refl (LoFTerm.toSKY t)
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans (step_toSKY hstep) ih

end LoFStep

/-! ## Alternate convention: “spec table” naming (Mark↦K, Unmark↦S) -/

namespace LoFStepSpec

open LoFTerm

/-- One-step reduction rules, but using the *spec-table* naming convention.

Definitionally: this is `LoFStep.Step` after swapping `mark` and `unmark` everywhere. -/
abbrev Step (t u : LoFTerm) : Prop :=
  LoFStep.Step (swapMarkUnmark t) (swapMarkUnmark u)

/-- Multi-step reachability under the spec-table naming convention. -/
abbrev Steps (t u : LoFTerm) : Prop :=
  LoFStep.Steps (swapMarkUnmark t) (swapMarkUnmark u)

open HeytingLean.LoF.Comb

theorem step_toSKY_spec {t u : LoFTerm} :
    Step t u → Comb.Step (LoFTerm.toSKY_spec t) (LoFTerm.toSKY_spec u) := by
  intro h
  -- Unfold the two “spec naming” abbreviations and reuse the existing proof.
  simpa [Step, LoFTerm.toSKY_spec] using (LoFStep.step_toSKY (t := swapMarkUnmark t) (u := swapMarkUnmark u) h)

theorem steps_toSKY_spec {t u : LoFTerm} :
    Steps t u → Comb.Steps (LoFTerm.toSKY_spec t) (LoFTerm.toSKY_spec u) := by
  intro h
  simpa [Steps, LoFTerm.toSKY_spec] using (LoFStep.steps_toSKY (t := swapMarkUnmark t) (u := swapMarkUnmark u) h)

end LoFStepSpec

end Correspondence
end LoF
end HeytingLean
