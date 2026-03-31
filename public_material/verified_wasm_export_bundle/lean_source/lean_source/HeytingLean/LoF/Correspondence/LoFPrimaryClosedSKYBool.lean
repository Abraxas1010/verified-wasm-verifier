import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.LoFPrimary.Normalization

/-!
# LoFPrimaryClosedSKYBool — a closed-fragment bridge from primary LoF to SKY booleans

This file addresses (a small but concrete part of) the outstanding “LoF ↔ SKY” gap:

- `LoFPrimary` gives a Boolean semantics for Spencer–Brown’s *primary algebra* fragment
  (`void`, `mark`, `juxt`) with rewrite rules (calling/crossing/void absorption).
- `SKY` (`K/S/Y`) is a combinator rewrite system.

The full, variable-dependent correspondence is a large project (requires a notion of variables /
environments on the SKY side). Here we implement an **honest closed-fragment bridge**; for the
variable-dependent and env-free extensions in this repo, see:

* `LoFPrimarySKYBool` (env-parametrized, produces a closed SKY boolean), and
* `LoFPrimarySKYBoolNary` (env-free `n`-ary compilation).

- for `A : LoFPrimary.Expr 0` (no free variables), we translate `A` to a SKY term that behaves as a
  Church-boolean;
- we prove it reduces to the canonical boolean (`true`/`false`) matching `LoFPrimary.eval A`.

This is enough to certify that primary rewrite steps on *closed* expressions preserve the SKY
boolean meaning (because `LoFPrimary.step_sound` preserves `eval`).
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.LoFPrimary

open LoFPrimary.Expr

/-! ## Convenience lemmas for multi-step reduction -/

namespace StepsLemmas

theorem steps_transitive {t u v : Comb} : Comb.Steps t u → Comb.Steps u v → Comb.Steps t v := by
  intro htu huv
  induction htu with
  | refl _ =>
      simpa using huv
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans hstep (ih huv)

theorem steps_app_left {f f' a : Comb} :
    Comb.Steps f f' → Comb.Steps (Comb.app f a) (Comb.app f' a) := by
  intro h
  induction h with
  | refl f =>
      exact Comb.Steps.refl (Comb.app f a)
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans (Comb.Step.app_left hstep) ih

theorem steps_app_right {f a a' : Comb} :
    Comb.Steps a a' → Comb.Steps (Comb.app f a) (Comb.app f a') := by
  intro h
  induction h with
  | refl a =>
      exact Comb.Steps.refl (Comb.app f a)
  | trans hstep hsteps ih =>
      exact Comb.Steps.trans (Comb.Step.app_right hstep) ih

theorem steps_congr_app {f f' a a' : Comb} (hf : Comb.Steps f f') (ha : Comb.Steps a a') :
    Comb.Steps (Comb.app f a) (Comb.app f' a') := by
  exact steps_transitive (steps_app_left (a := a) hf) (steps_app_right (f := f') ha)

end StepsLemmas

/-! ## SKY booleans (Church encoding in `K/S`) -/

namespace SKYBool

/-- `true` as a selector: `true x y ↦ x`. -/
def tt : Comb := .K

/-- `false` as a selector: `false x y ↦ y`. -/
def ff : Comb := .app .K .I

/-- Turn a Boolean value into its SKY boolean term. -/
def ofBool : Bool → Comb
  | true => tt
  | false => ff

@[simp] theorem ofBool_true : ofBool true = tt := rfl
@[simp] theorem ofBool_false : ofBool false = ff := rfl

/-- A non-recursive closed environment for `Fin 0`. -/
def env0 : Fin 0 → Bool := Fin.elim0

/-! ### Boolean selectors reduce correctly -/

open Comb.Steps

theorem tt_select (x y : Comb) : Comb.Steps (Comb.app (Comb.app tt x) y) x := by
  exact Comb.Steps.trans (Comb.Step.K_rule (x := x) (y := y)) (Comb.Steps.refl x)

theorem ff_select (x y : Comb) : Comb.Steps (Comb.app (Comb.app ff x) y) y := by
  -- ((K I) x) y  ↦  (I) y  ↦  y
  have h₁ : Comb.Steps (Comb.app (Comb.app ff x) y) (Comb.app Comb.I y) := by
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    -- Lift the root `K`-reduction through the outer application.
    exact Comb.Step.app_left (Comb.Step.K_rule (x := Comb.I) (y := x))
  exact StepsLemmas.steps_transitive h₁ (Comb.I_reduces y)

/-! ## NOT and OR on SKY booleans -/

/-- Boolean negation: `not b = b ff tt`. -/
def not : Comb :=
  -- λb. b ff tt  ↦  S (S I (K ff)) (K tt)
  Comb.app (Comb.app .S (Comb.app (Comb.app .S .I) (Comb.app .K ff))) (Comb.app .K tt)

/-- Closed-form reduction: `not b ↦* b ff tt`. -/
theorem not_reduces (b : Comb) :
    Comb.Steps (Comb.app not b) (Comb.app (Comb.app b ff) tt) := by
  -- Expand the SK reduction sequence.
  -- (S X Y) b ↦ X b (Y b)
  let X : Comb := Comb.app (Comb.app .S .I) (Comb.app .K ff)
  let Yterm : Comb := Comb.app .K tt
  have h1 : Comb.Steps (Comb.app not b) (Comb.app (Comb.app X b) (Comb.app Yterm b)) := by
    -- One S-step at the root.
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    simpa [not, X, Yterm] using Comb.Step.S_rule (x := X) (y := Yterm) (z := b)
  -- Reduce `Y b ↦ tt`.
  have hY : Comb.Steps (Comb.app Yterm b) tt := by
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    simpa [Yterm] using Comb.Step.K_rule (x := tt) (y := b)
  -- Reduce `X b ↦* b ff`.
  have hX : Comb.Steps (Comb.app X b) (Comb.app b ff) := by
    -- X b = (S I (K ff)) b ↦ I b ((K ff) b) ↦ b ff
    have hX1 : Comb.Steps (Comb.app X b) (Comb.app (Comb.app .I b) (Comb.app (Comb.app .K ff) b)) := by
      refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
      simpa [X] using
        Comb.Step.S_rule (x := Comb.I) (y := Comb.app Comb.K ff) (z := b)
    have hX2 : Comb.Steps (Comb.app (Comb.app .I b) (Comb.app (Comb.app .K ff) b))
        (Comb.app b (Comb.app (Comb.app .K ff) b)) := by
      exact StepsLemmas.steps_app_left (a := Comb.app (Comb.app Comb.K ff) b) (Comb.I_reduces b)
    have hX3 : Comb.Steps (Comb.app (Comb.app .K ff) b) ff := by
      refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
      simpa using Comb.Step.K_rule (x := ff) (y := b)
    have hX4 : Comb.Steps (Comb.app b (Comb.app (Comb.app .K ff) b)) (Comb.app b ff) := by
      exact StepsLemmas.steps_app_right (f := b) hX3
    exact StepsLemmas.steps_transitive hX1 (StepsLemmas.steps_transitive hX2 hX4)
  -- Combine, using congruence under application.
  have h2 :
      Comb.Steps (Comb.app (Comb.app X b) (Comb.app Yterm b)) (Comb.app (Comb.app b ff) tt) := by
    -- First reduce left, then right.
    exact (StepsLemmas.steps_congr_app (hf := hX) (ha := hY))
  exact StepsLemmas.steps_transitive h1 h2

theorem not_tt : Comb.Steps (Comb.app not tt) ff := by
  -- not tt ↦* tt ff tt ↦ ff
  have h : Comb.Steps (Comb.app not tt) (Comb.app (Comb.app tt ff) tt) :=
    not_reduces tt
  have hsel : Comb.Steps (Comb.app (Comb.app tt ff) tt) ff :=
    tt_select ff tt
  exact StepsLemmas.steps_transitive h hsel

theorem not_ff : Comb.Steps (Comb.app not ff) tt := by
  -- not ff ↦* ff ff tt ↦ tt
  have h : Comb.Steps (Comb.app not ff) (Comb.app (Comb.app ff ff) tt) :=
    not_reduces ff
  have hsel : Comb.Steps (Comb.app (Comb.app ff ff) tt) tt :=
    ff_select ff tt
  exact StepsLemmas.steps_transitive h hsel

/-! ### OR on SKY booleans (left-biased selector formula) -/

theorem or_tt (q : Comb) : Comb.Steps (Comb.app (Comb.app tt tt) q) tt := by
  -- tt tt q = K tt q ↦ tt
  exact tt_select tt q

theorem or_ff (q : Comb) : Comb.Steps (Comb.app (Comb.app ff ff) q) q := by
  -- ff ff q ↦ q
  exact ff_select ff q

end SKYBool

/-! ## Translation of closed primary expressions -/

namespace LoFPrimaryClosed

open SKYBool
open Comb.Steps

/-- Translate a closed primary expression (`n = 0`) to a SKY boolean term. -/
def toSKYBool : LoFPrimary.Expr 0 → Comb
  | .void => ff
  | .var i => (Fin.elim0 i)
  | .mark A => Comb.app SKYBool.not (toSKYBool A)
  | .juxt A B =>
      -- `or p q = p p q`
      Comb.app (Comb.app (toSKYBool A) (toSKYBool A)) (toSKYBool B)

/-- Closed evaluation (unique environment). -/
def eval0 (A : LoFPrimary.Expr 0) : Bool :=
  LoFPrimary.eval (n := 0) A SKYBool.env0

/-! ### Correctness: translation reduces to the canonical boolean -/

theorem toSKYBool_correct (A : LoFPrimary.Expr 0) :
    Comb.Steps (toSKYBool A) (SKYBool.ofBool (eval0 A)) := by
  induction A with
  | void =>
      -- `eval0 void = false`, so both sides are `ff`.
      simpa [toSKYBool, eval0, LoFPrimary.eval, SKYBool.ofBool, SKYBool.ff, SKYBool.tt] using
        (Comb.Steps.refl SKYBool.ff)
  | var i =>
      exact (Fin.elim0 i)
  | mark A ih =>
      -- Reduce argument to canonical boolean, then compute NOT.
      have hArg : Comb.Steps (toSKYBool A) (SKYBool.ofBool (eval0 A)) := ih
      have hCong :
        Comb.Steps (Comb.app SKYBool.not (toSKYBool A))
            (Comb.app SKYBool.not (SKYBool.ofBool (eval0 A))) :=
        StepsLemmas.steps_app_right (f := SKYBool.not) hArg
      cases hA : eval0 A with
      | false =>
          have hCong' :
              Comb.Steps (Comb.app SKYBool.not (toSKYBool A)) (Comb.app SKYBool.not SKYBool.ff) := by
            simpa [SKYBool.ofBool, hA] using hCong
          have hTot : Comb.Steps (Comb.app SKYBool.not (toSKYBool A)) SKYBool.tt :=
            StepsLemmas.steps_transitive hCong' SKYBool.not_ff
          have heval : SKYBool.ofBool (eval0 (Expr.mark A)) = SKYBool.tt := by
            have hA0 : LoFPrimary.eval (n := 0) A SKYBool.env0 = false := by
              simpa [eval0] using hA
            simp [eval0, LoFPrimary.eval, SKYBool.ofBool, hA0]
          simpa [toSKYBool, heval] using hTot
      | true =>
          have hCong' :
              Comb.Steps (Comb.app SKYBool.not (toSKYBool A)) (Comb.app SKYBool.not SKYBool.tt) := by
            simpa [SKYBool.ofBool, hA] using hCong
          have hTot : Comb.Steps (Comb.app SKYBool.not (toSKYBool A)) SKYBool.ff :=
            StepsLemmas.steps_transitive hCong' SKYBool.not_tt
          have heval : SKYBool.ofBool (eval0 (Expr.mark A)) = SKYBool.ff := by
            have hA0 : LoFPrimary.eval (n := 0) A SKYBool.env0 = true := by
              simpa [eval0] using hA
            simp [eval0, LoFPrimary.eval, SKYBool.ofBool, hA0]
          simpa [toSKYBool, heval] using hTot
  | juxt A B ihA ihB =>
      -- Reduce both operands to canonical booleans, then compute OR via `p p q`.
      have hA : Comb.Steps (toSKYBool A) (SKYBool.ofBool (eval0 A)) := ihA
      have hB : Comb.Steps (toSKYBool B) (SKYBool.ofBool (eval0 B)) := ihB
      -- First reduce the function occurrence of `toSKYBool A` in `(A A)`.
      have hAA1 :
        Comb.Steps (Comb.app (toSKYBool A) (toSKYBool A))
            (Comb.app (SKYBool.ofBool (eval0 A)) (toSKYBool A)) :=
        StepsLemmas.steps_app_left (a := toSKYBool A) hA
      -- Then reduce the argument occurrence of `toSKYBool A` in `(A A)`.
      have hAA2 :
        Comb.Steps (Comb.app (SKYBool.ofBool (eval0 A)) (toSKYBool A))
            (Comb.app (SKYBool.ofBool (eval0 A)) (SKYBool.ofBool (eval0 A))) :=
        StepsLemmas.steps_app_right (f := SKYBool.ofBool (eval0 A)) hA
      have hAA :
          Comb.Steps (Comb.app (toSKYBool A) (toSKYBool A))
            (Comb.app (SKYBool.ofBool (eval0 A)) (SKYBool.ofBool (eval0 A))) :=
        StepsLemmas.steps_transitive hAA1 hAA2
      -- Now reduce the outer application by congruence, then reduce `B`.
      have hOuter1 :
        Comb.Steps
            (Comb.app (Comb.app (toSKYBool A) (toSKYBool A)) (toSKYBool B))
            (Comb.app (Comb.app (SKYBool.ofBool (eval0 A)) (SKYBool.ofBool (eval0 A))) (toSKYBool B)) :=
        StepsLemmas.steps_app_left (a := toSKYBool B) hAA
      have hOuter2 :
        Comb.Steps
            (Comb.app (Comb.app (SKYBool.ofBool (eval0 A)) (SKYBool.ofBool (eval0 A))) (toSKYBool B))
            (Comb.app (Comb.app (SKYBool.ofBool (eval0 A)) (SKYBool.ofBool (eval0 A)))
              (SKYBool.ofBool (eval0 B))) :=
        StepsLemmas.steps_app_right (f := Comb.app (SKYBool.ofBool (eval0 A)) (SKYBool.ofBool (eval0 A)))
          hB
      have hOuter : Comb.Steps (toSKYBool (Expr.juxt A B))
          (Comb.app (Comb.app (SKYBool.ofBool (eval0 A)) (SKYBool.ofBool (eval0 A)))
            (SKYBool.ofBool (eval0 B))) := by
        simpa [toSKYBool] using (StepsLemmas.steps_transitive hOuter1 hOuter2)
      -- Finish by cases on `eval0 A` and `eval0 B`.
      cases hEa : eval0 A with
      | false =>
          cases hEb : eval0 B with
          | false =>
              have hOuter' :
                  Comb.Steps (toSKYBool (Expr.juxt A B)) (Comb.app (Comb.app SKYBool.ff SKYBool.ff) SKYBool.ff) := by
                simpa [SKYBool.ofBool, hEa, hEb] using hOuter
              have hsel : Comb.Steps (Comb.app (Comb.app SKYBool.ff SKYBool.ff) SKYBool.ff) SKYBool.ff :=
                SKYBool.or_ff SKYBool.ff
              have hTot : Comb.Steps (toSKYBool (Expr.juxt A B)) SKYBool.ff :=
                StepsLemmas.steps_transitive hOuter' hsel
              have heval : SKYBool.ofBool (eval0 (Expr.juxt A B)) = SKYBool.ff := by
                have hEa0 : LoFPrimary.eval (n := 0) A SKYBool.env0 = false := by
                  simpa [eval0] using hEa
                have hEb0 : LoFPrimary.eval (n := 0) B SKYBool.env0 = false := by
                  simpa [eval0] using hEb
                simp [eval0, LoFPrimary.eval, SKYBool.ofBool, hEa0, hEb0]
              simpa [toSKYBool, heval] using hTot
          | true =>
              have hOuter' :
                  Comb.Steps (toSKYBool (Expr.juxt A B)) (Comb.app (Comb.app SKYBool.ff SKYBool.ff) SKYBool.tt) := by
                simpa [SKYBool.ofBool, hEa, hEb] using hOuter
              have hsel : Comb.Steps (Comb.app (Comb.app SKYBool.ff SKYBool.ff) SKYBool.tt) SKYBool.tt :=
                SKYBool.or_ff SKYBool.tt
              have hTot : Comb.Steps (toSKYBool (Expr.juxt A B)) SKYBool.tt :=
                StepsLemmas.steps_transitive hOuter' hsel
              have heval : SKYBool.ofBool (eval0 (Expr.juxt A B)) = SKYBool.tt := by
                have hEa0 : LoFPrimary.eval (n := 0) A SKYBool.env0 = false := by
                  simpa [eval0] using hEa
                have hEb0 : LoFPrimary.eval (n := 0) B SKYBool.env0 = true := by
                  simpa [eval0] using hEb
                simp [eval0, LoFPrimary.eval, SKYBool.ofBool, hEa0, hEb0]
              simpa [toSKYBool, heval] using hTot
      | true =>
          cases hEb : eval0 B with
          | false =>
              have hOuter' :
                  Comb.Steps (toSKYBool (Expr.juxt A B)) (Comb.app (Comb.app SKYBool.tt SKYBool.tt) SKYBool.ff) := by
                simpa [SKYBool.ofBool, hEa, hEb] using hOuter
              have hsel : Comb.Steps (Comb.app (Comb.app SKYBool.tt SKYBool.tt) SKYBool.ff) SKYBool.tt :=
                SKYBool.or_tt SKYBool.ff
              have hTot : Comb.Steps (toSKYBool (Expr.juxt A B)) SKYBool.tt :=
                StepsLemmas.steps_transitive hOuter' hsel
              have heval : SKYBool.ofBool (eval0 (Expr.juxt A B)) = SKYBool.tt := by
                have hEa0 : LoFPrimary.eval (n := 0) A SKYBool.env0 = true := by
                  simpa [eval0] using hEa
                have hEb0 : LoFPrimary.eval (n := 0) B SKYBool.env0 = false := by
                  simpa [eval0] using hEb
                simp [eval0, LoFPrimary.eval, SKYBool.ofBool, hEa0, hEb0]
              simpa [toSKYBool, heval] using hTot
          | true =>
              have hOuter' :
                  Comb.Steps (toSKYBool (Expr.juxt A B)) (Comb.app (Comb.app SKYBool.tt SKYBool.tt) SKYBool.tt) := by
                simpa [SKYBool.ofBool, hEa, hEb] using hOuter
              have hsel : Comb.Steps (Comb.app (Comb.app SKYBool.tt SKYBool.tt) SKYBool.tt) SKYBool.tt :=
                SKYBool.or_tt SKYBool.tt
              have hTot : Comb.Steps (toSKYBool (Expr.juxt A B)) SKYBool.tt :=
                StepsLemmas.steps_transitive hOuter' hsel
              have heval : SKYBool.ofBool (eval0 (Expr.juxt A B)) = SKYBool.tt := by
                have hEa0 : LoFPrimary.eval (n := 0) A SKYBool.env0 = true := by
                  simpa [eval0] using hEa
                have hEb0 : LoFPrimary.eval (n := 0) B SKYBool.env0 = true := by
                  simpa [eval0] using hEb
                simp [eval0, LoFPrimary.eval, SKYBool.ofBool, hEa0, hEb0]
              simpa [toSKYBool, heval] using hTot

end LoFPrimaryClosed

end Correspondence
end LoF
end HeytingLean
