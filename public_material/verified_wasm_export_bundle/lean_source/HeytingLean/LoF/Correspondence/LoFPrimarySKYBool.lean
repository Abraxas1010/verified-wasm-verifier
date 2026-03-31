import HeytingLean.LoF.Correspondence.LoFPrimaryClosedSKYBool

/-!
# LoFPrimarySKYBool — LoFPrimary with variables → SKY Church booleans (via environments)

`LoFPrimaryClosedSKYBool` gives a proven bridge for closed expressions `Expr 0`.

This file extends that bridge to expressions with free variables, *by parameterizing the
translation by a Boolean environment* `ρ : Fin n → Bool`:

* variables are interpreted as their Boolean values under `ρ`,
* the translation produces a **closed** SKY term (no free variables on the SKY side),
* and we prove that it reduces to the canonical Church boolean matching `LoFPrimary.eval A ρ`.

This file deliberately stays env-parametrized: it does **not** attempt to produce a single SKY term representing
an `n`-ary Boolean function. For the env-free `n`-ary compilation in this repo, see
`LoFPrimarySKYBoolNary`.
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.LoFPrimary

open LoFPrimary.Expr

open StepsLemmas
open SKYBool

namespace LoFPrimarySKYBool

/-! ## Translation (environment-parametrized) -/

/-- Translate a primary expression under a Boolean environment into a SKY Church boolean term. -/
def toSKYBool {n : Nat} : LoFPrimary.Expr n → (Fin n → Bool) → Comb
  | .void, _ => SKYBool.ff
  | .var i, ρ => SKYBool.ofBool (ρ i)
  | .mark A, ρ => Comb.app SKYBool.not (toSKYBool A ρ)
  | .juxt A B, ρ =>
      -- OR via selector: `or p q = p p q`
      Comb.app (Comb.app (toSKYBool A ρ) (toSKYBool A ρ)) (toSKYBool B ρ)

/-! ## Boolean algebra lemmas for the SKY encoding -/

theorem not_ofBool (b : Bool) :
    Comb.Steps (Comb.app SKYBool.not (SKYBool.ofBool b)) (SKYBool.ofBool (!b)) := by
  cases b with
  | false =>
      simpa [SKYBool.ofBool] using SKYBool.not_ff
  | true =>
      simpa [SKYBool.ofBool] using SKYBool.not_tt

theorem not_reduces {p : Comb} {b : Bool} (hp : Comb.Steps p (SKYBool.ofBool b)) :
    Comb.Steps (Comb.app SKYBool.not p) (SKYBool.ofBool (!b)) := by
  have hcong :
      Comb.Steps (Comb.app SKYBool.not p) (Comb.app SKYBool.not (SKYBool.ofBool b)) :=
    StepsLemmas.steps_app_right (f := SKYBool.not) hp
  exact StepsLemmas.steps_transitive hcong (not_ofBool b)

theorem or_ofBool (b c : Bool) :
    Comb.Steps
      (Comb.app (Comb.app (SKYBool.ofBool b) (SKYBool.ofBool b)) (SKYBool.ofBool c))
      (SKYBool.ofBool (b || c)) := by
  cases b with
  | true =>
      have h :
          Comb.Steps (Comb.app (Comb.app SKYBool.tt SKYBool.tt) (SKYBool.ofBool c)) SKYBool.tt :=
        SKYBool.or_tt (SKYBool.ofBool c)
      simpa [SKYBool.ofBool] using h
  | false =>
      have h :
          Comb.Steps (Comb.app (Comb.app SKYBool.ff SKYBool.ff) (SKYBool.ofBool c)) (SKYBool.ofBool c) :=
        SKYBool.or_ff (SKYBool.ofBool c)
      simpa [SKYBool.ofBool] using h

theorem or_reduces {p q : Comb} {b c : Bool} (hp : Comb.Steps p (SKYBool.ofBool b))
    (hq : Comb.Steps q (SKYBool.ofBool c)) :
    Comb.Steps (Comb.app (Comb.app p p) q) (SKYBool.ofBool (b || c)) := by
  -- First reduce the two occurrences of `p` in `p p`.
  have hpp1 : Comb.Steps (Comb.app p p) (Comb.app (SKYBool.ofBool b) p) :=
    StepsLemmas.steps_app_left (a := p) hp
  have hpp2 :
      Comb.Steps (Comb.app (SKYBool.ofBool b) p) (Comb.app (SKYBool.ofBool b) (SKYBool.ofBool b)) :=
    StepsLemmas.steps_app_right (f := SKYBool.ofBool b) hp
  have hpp :
      Comb.Steps (Comb.app p p) (Comb.app (SKYBool.ofBool b) (SKYBool.ofBool b)) :=
    StepsLemmas.steps_transitive hpp1 hpp2

  -- Lift that to the outer application, then reduce `q`.
  have houter1 :
      Comb.Steps
        (Comb.app (Comb.app p p) q)
        (Comb.app (Comb.app (SKYBool.ofBool b) (SKYBool.ofBool b)) q) :=
    StepsLemmas.steps_app_left (a := q) hpp
  have houter2 :
      Comb.Steps
        (Comb.app (Comb.app (SKYBool.ofBool b) (SKYBool.ofBool b)) q)
        (Comb.app (Comb.app (SKYBool.ofBool b) (SKYBool.ofBool b)) (SKYBool.ofBool c)) :=
    StepsLemmas.steps_app_right (f := Comb.app (SKYBool.ofBool b) (SKYBool.ofBool b)) hq
  have houter :
      Comb.Steps
        (Comb.app (Comb.app p p) q)
        (Comb.app (Comb.app (SKYBool.ofBool b) (SKYBool.ofBool b)) (SKYBool.ofBool c)) :=
    StepsLemmas.steps_transitive houter1 houter2

  exact StepsLemmas.steps_transitive houter (or_ofBool b c)

/-! ## Correctness theorem -/

theorem toSKYBool_correct {n : Nat} (A : LoFPrimary.Expr n) :
    ∀ ρ : Fin n → Bool, Comb.Steps (toSKYBool A ρ) (SKYBool.ofBool (LoFPrimary.eval A ρ)) := by
  induction A with
  | void =>
      intro ρ
      simpa [toSKYBool, LoFPrimary.eval, SKYBool.ofBool] using (Comb.Steps.refl SKYBool.ff)
  | var i =>
      intro ρ
      simpa [toSKYBool, LoFPrimary.eval] using (Comb.Steps.refl (SKYBool.ofBool (ρ i)))
  | mark A ih =>
      intro ρ
      have hp : Comb.Steps (toSKYBool A ρ) (SKYBool.ofBool (LoFPrimary.eval A ρ)) := ih ρ
      have hnot :
          Comb.Steps (Comb.app SKYBool.not (toSKYBool A ρ)) (SKYBool.ofBool (!(LoFPrimary.eval A ρ))) :=
        not_reduces (p := toSKYBool A ρ) (b := LoFPrimary.eval A ρ) hp
      simpa [toSKYBool, LoFPrimary.eval] using hnot
  | juxt A B ihA ihB =>
      intro ρ
      have hp : Comb.Steps (toSKYBool A ρ) (SKYBool.ofBool (LoFPrimary.eval A ρ)) := ihA ρ
      have hq : Comb.Steps (toSKYBool B ρ) (SKYBool.ofBool (LoFPrimary.eval B ρ)) := ihB ρ
      have hor :
          Comb.Steps
            (Comb.app (Comb.app (toSKYBool A ρ) (toSKYBool A ρ)) (toSKYBool B ρ))
            (SKYBool.ofBool (LoFPrimary.eval A ρ || LoFPrimary.eval B ρ)) :=
        or_reduces
          (p := toSKYBool A ρ)
          (q := toSKYBool B ρ)
          (b := LoFPrimary.eval A ρ)
          (c := LoFPrimary.eval B ρ)
          hp
          hq
      simpa [toSKYBool, LoFPrimary.eval] using hor

end LoFPrimarySKYBool

end Correspondence
end LoF
end HeytingLean
