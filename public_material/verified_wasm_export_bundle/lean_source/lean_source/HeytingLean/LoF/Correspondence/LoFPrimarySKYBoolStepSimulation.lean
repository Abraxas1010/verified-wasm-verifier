import HeytingLean.LoF.Correspondence.LoFPrimarySKYBool

/-!
# LoFPrimarySKYBoolStepSimulation — what LoFPrimary rewrites can (and cannot) simulate in SKY

The primary LoF rewrite system (`LoFPrimary.Step`) includes laws that are semantically valid in the
Boolean interpretation (`void=false`, `mark=not`, `juxt=or`). Under the Church-boolean SKY encoding,
some of these laws correspond to directed reductions, while others are only valid up to *observational*
equivalence (joinability after applying arguments).

This file provides:

* **Positive results**: a small “step simulation” layer where SKY reduction genuinely yields the RHS
  term (not merely the same boolean normal form).
* **Impossibility witness**: distinct *normal forms* can be observationally equivalent as booleans,
  so reduction cannot in general serve as the equality notion for boolean laws.
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.LoFPrimary

open StepsLemmas
open SKYBool

namespace LoFPrimarySKYBoolStepSimulation

/-! ## Joinability / observational equivalence -/

/-- Two SKY terms are joinable if they both reduce to a common term. -/
def Joinable (t u : Comb) : Prop :=
  ∃ w : Comb, Comb.Steps t w ∧ Comb.Steps u w

/-- Boolean observational equivalence: joinable after applying two arguments. -/
def BoolObsEq (p q : Comb) : Prop :=
  ∀ x y : Comb, Joinable (Comb.app (Comb.app p x) y) (Comb.app (Comb.app q x) y)

theorem boolObsEq_of_steps_ofBool {p q : Comb} {b : Bool}
    (hp : Comb.Steps p (SKYBool.ofBool b)) (hq : Comb.Steps q (SKYBool.ofBool b)) :
    BoolObsEq p q := by
  intro x y
  cases b with
  | false =>
      refine ⟨y, ?_, ?_⟩
      · have hp1 : Comb.Steps (Comb.app p x) (Comb.app (SKYBool.ofBool false) x) :=
          steps_app_left (a := x) hp
        have hp2 :
            Comb.Steps (Comb.app (Comb.app p x) y) (Comb.app (Comb.app (SKYBool.ofBool false) x) y) :=
          steps_app_left (a := y) hp1
        have hsel : Comb.Steps (Comb.app (Comb.app (SKYBool.ofBool false) x) y) y := by
          simpa [SKYBool.ofBool] using SKYBool.ff_select (x := x) (y := y)
        exact steps_transitive hp2 hsel
      · have hq1 : Comb.Steps (Comb.app q x) (Comb.app (SKYBool.ofBool false) x) :=
          steps_app_left (a := x) hq
        have hq2 :
            Comb.Steps (Comb.app (Comb.app q x) y) (Comb.app (Comb.app (SKYBool.ofBool false) x) y) :=
          steps_app_left (a := y) hq1
        have hsel : Comb.Steps (Comb.app (Comb.app (SKYBool.ofBool false) x) y) y := by
          simpa [SKYBool.ofBool] using SKYBool.ff_select (x := x) (y := y)
        exact steps_transitive hq2 hsel
  | true =>
      refine ⟨x, ?_, ?_⟩
      · have hp1 : Comb.Steps (Comb.app p x) (Comb.app (SKYBool.ofBool true) x) :=
          steps_app_left (a := x) hp
        have hp2 :
            Comb.Steps (Comb.app (Comb.app p x) y) (Comb.app (Comb.app (SKYBool.ofBool true) x) y) :=
          steps_app_left (a := y) hp1
        have hsel : Comb.Steps (Comb.app (Comb.app (SKYBool.ofBool true) x) y) x := by
          simpa [SKYBool.ofBool] using SKYBool.tt_select (x := x) (y := y)
        exact steps_transitive hp2 hsel
      · have hq1 : Comb.Steps (Comb.app q x) (Comb.app (SKYBool.ofBool true) x) :=
          steps_app_left (a := x) hq
        have hq2 :
            Comb.Steps (Comb.app (Comb.app q x) y) (Comb.app (Comb.app (SKYBool.ofBool true) x) y) :=
          steps_app_left (a := y) hq1
        have hsel : Comb.Steps (Comb.app (Comb.app (SKYBool.ofBool true) x) y) x := by
          simpa [SKYBool.ofBool] using SKYBool.tt_select (x := x) (y := y)
        exact steps_transitive hq2 hsel

/-! ## A basic “normal forms don’t go anywhere” lemma -/

theorem eq_of_steps_of_normal {t u : Comb} (ht : Comb.Normal t) (h : Comb.Steps t u) : u = t := by
  induction h with
  | refl _ => rfl
  | trans hstep _ _ =>
      exact (False.elim <| ht _ hstep)

theorem not_steps_of_normal_ne {t u : Comb} (ht : Comb.Normal t) (hne : t ≠ u) :
    ¬ Comb.Steps t u := by
  intro h
  exact hne (eq_of_steps_of_normal (t := t) (u := u) ht h).symm

/-! ## Alternative normal-form booleans (impossibility witness) -/

/-- An alternative “true” boolean in SKY: `S (K tt) I`. -/
def trueAlt : Comb :=
  Comb.app (Comb.app .S (Comb.app .K SKYBool.tt)) Comb.I

/-- An alternative “false” boolean in SKY: `S (K ff) I`. -/
def falseAlt : Comb :=
  Comb.app (Comb.app .S (Comb.app .K SKYBool.ff)) Comb.I

/-! ### Normal forms used for the impossibility witness -/

theorem I_normal : Comb.Normal Comb.I := by
  simpa [Comb.I] using Comb.S_app_app_normal Comb.K_normal Comb.K_normal

theorem ff_normal : Comb.Normal SKYBool.ff := by
  simpa [SKYBool.ff] using Comb.K_app_normal I_normal

theorem trueAlt_select (x y : Comb) :
    Comb.Steps (Comb.app (Comb.app trueAlt x) y) x := by
  -- (S (K tt) I) x y  ↦  ((K tt) x) (I x) y  ↦  (tt) (I x) y  ↦  I x  ↦*  x
  have hS :
      Comb.Steps (Comb.app (Comb.app trueAlt x) y)
        (Comb.app (Comb.app (Comb.app (Comb.app .K SKYBool.tt) x) (Comb.app Comb.I x)) y) := by
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    exact
      Comb.Step.app_left
        (Comb.Step.S_rule (x := Comb.app Comb.K SKYBool.tt) (y := Comb.I) (z := x))
  have hKtt : Comb.Steps (Comb.app (Comb.app .K SKYBool.tt) x) SKYBool.tt := by
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    simpa using Comb.Step.K_rule (x := SKYBool.tt) (y := x)
  have h1 :
      Comb.Steps
        (Comb.app (Comb.app (Comb.app (Comb.app .K SKYBool.tt) x) (Comb.app Comb.I x)) y)
        (Comb.app (Comb.app SKYBool.tt (Comb.app Comb.I x)) y) := by
    have hfun :
        Comb.Steps
          (Comb.app (Comb.app (Comb.app .K SKYBool.tt) x) (Comb.app Comb.I x))
          (Comb.app SKYBool.tt (Comb.app Comb.I x)) :=
      steps_app_left (a := Comb.app Comb.I x) hKtt
    exact steps_app_left (a := y) hfun
  have hSel : Comb.Steps (Comb.app (Comb.app SKYBool.tt (Comb.app Comb.I x)) y) (Comb.app Comb.I x) :=
    SKYBool.tt_select (x := Comb.app Comb.I x) (y := y)
  exact steps_transitive hS (steps_transitive h1 (steps_transitive hSel (Comb.I_reduces x)))

theorem falseAlt_select (x y : Comb) :
    Comb.Steps (Comb.app (Comb.app falseAlt x) y) y := by
  -- (S (K ff) I) x y  ↦  ((K ff) x) (I x) y  ↦  (ff) (I x) y  ↦  y
  have hS :
      Comb.Steps (Comb.app (Comb.app falseAlt x) y)
        (Comb.app (Comb.app (Comb.app (Comb.app .K SKYBool.ff) x) (Comb.app Comb.I x)) y) := by
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    exact
      Comb.Step.app_left
        (Comb.Step.S_rule (x := Comb.app Comb.K SKYBool.ff) (y := Comb.I) (z := x))
  have hKff : Comb.Steps (Comb.app (Comb.app .K SKYBool.ff) x) SKYBool.ff := by
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    simpa using Comb.Step.K_rule (x := SKYBool.ff) (y := x)
  have h1 :
      Comb.Steps
        (Comb.app (Comb.app (Comb.app (Comb.app .K SKYBool.ff) x) (Comb.app Comb.I x)) y)
        (Comb.app (Comb.app SKYBool.ff (Comb.app Comb.I x)) y) := by
    have hfun :
        Comb.Steps
          (Comb.app (Comb.app (Comb.app .K SKYBool.ff) x) (Comb.app Comb.I x))
          (Comb.app SKYBool.ff (Comb.app Comb.I x)) :=
      steps_app_left (a := Comb.app Comb.I x) hKff
    exact steps_app_left (a := y) hfun
  have hSel : Comb.Steps (Comb.app (Comb.app SKYBool.ff (Comb.app Comb.I x)) y) y :=
    SKYBool.ff_select (x := Comb.app Comb.I x) (y := y)
  exact steps_transitive hS (steps_transitive h1 hSel)

theorem trueAlt_obsEq_tt : BoolObsEq trueAlt SKYBool.tt := by
  intro x y
  refine ⟨x, trueAlt_select (x := x) (y := y), ?_⟩
  exact SKYBool.tt_select (x := x) (y := y)

theorem falseAlt_obsEq_ff : BoolObsEq falseAlt SKYBool.ff := by
  intro x y
  refine ⟨y, falseAlt_select (x := x) (y := y), ?_⟩
  exact SKYBool.ff_select (x := x) (y := y)

theorem trueAlt_ne_tt : trueAlt ≠ SKYBool.tt := by
  decide

theorem falseAlt_ne_ff : falseAlt ≠ SKYBool.ff := by
  decide

theorem trueAlt_normal : Comb.Normal trueAlt := by
  have hKtt : Comb.Normal (Comb.app Comb.K SKYBool.tt) := Comb.K_app_normal Comb.K_normal
  show Comb.Normal (Comb.app (Comb.app Comb.S (Comb.app Comb.K SKYBool.tt)) Comb.I)
  exact Comb.S_app_app_normal hKtt I_normal

theorem falseAlt_normal : Comb.Normal falseAlt := by
  have hKff : Comb.Normal (Comb.app Comb.K SKYBool.ff) := Comb.K_app_normal ff_normal
  show Comb.Normal (Comb.app (Comb.app Comb.S (Comb.app Comb.K SKYBool.ff)) Comb.I)
  exact Comb.S_app_app_normal hKff I_normal

/-- Impossibility witness: observationally equivalent booleans need not reduce to each other. -/
theorem obsEq_not_steps (p q : Comb) (_hObs : BoolObsEq p q)
    (hp : Comb.Normal p) (hq : Comb.Normal q) (hne : p ≠ q) :
    (¬ Comb.Steps p q) ∧ (¬ Comb.Steps q p) := by
  refine ⟨not_steps_of_normal_ne (t := p) (u := q) hp hne, ?_⟩
  have hne' : q ≠ p := by exact Ne.symm hne
  exact not_steps_of_normal_ne (t := q) (u := p) hq hne'

theorem trueAlt_not_steps_tt : (¬ Comb.Steps trueAlt SKYBool.tt) ∧ (¬ Comb.Steps SKYBool.tt trueAlt) := by
  exact
    obsEq_not_steps
      (p := trueAlt)
      (q := SKYBool.tt)
      (_hObs := trueAlt_obsEq_tt)
      trueAlt_normal
      Comb.K_normal
      trueAlt_ne_tt

theorem falseAlt_not_steps_ff : (¬ Comb.Steps falseAlt SKYBool.ff) ∧ (¬ Comb.Steps SKYBool.ff falseAlt) := by
  exact
    obsEq_not_steps
      (p := falseAlt)
      (q := SKYBool.ff)
      (_hObs := falseAlt_obsEq_ff)
      falseAlt_normal
      ff_normal
      falseAlt_ne_ff

/-! ## Positive step-simulation results for LoFPrimary rewrites -/

open LoFPrimarySKYBool

/-- A SKY Church boolean used as `or p p` selects `p` itself. -/
theorem or_self_select {p : Comb} {b : Bool} (hp : Comb.Steps p (SKYBool.ofBool b)) :
    Comb.Steps (Comb.app (Comb.app p p) p) p := by
  cases b with
  | false =>
      have hLift :
          Comb.Steps (Comb.app (Comb.app p p) p)
            (Comb.app (Comb.app (SKYBool.ofBool false) p) p) := by
        have hpp : Comb.Steps (Comb.app p p) (Comb.app (SKYBool.ofBool false) p) :=
          steps_app_left (a := p) hp
        exact steps_app_left (a := p) hpp
      have hSel : Comb.Steps (Comb.app (Comb.app (SKYBool.ofBool false) p) p) p := by
        simpa [SKYBool.ofBool] using SKYBool.ff_select (x := p) (y := p)
      exact steps_transitive hLift hSel
  | true =>
      have hLift :
          Comb.Steps (Comb.app (Comb.app p p) p)
            (Comb.app (Comb.app (SKYBool.ofBool true) p) p) := by
        have hpp : Comb.Steps (Comb.app p p) (Comb.app (SKYBool.ofBool true) p) :=
          steps_app_left (a := p) hp
        exact steps_app_left (a := p) hpp
      have hSel : Comb.Steps (Comb.app (Comb.app (SKYBool.ofBool true) p) p) p := by
        simpa [SKYBool.ofBool] using SKYBool.tt_select (x := p) (y := p)
      exact steps_transitive hLift hSel

theorem calling_simulated {n : Nat} (A : LoFPrimary.Expr n) (ρ : Fin n → Bool) :
    Comb.Steps (toSKYBool (n := n) (Expr.juxt A A) ρ) (toSKYBool (n := n) A ρ) := by
  have hp : Comb.Steps (toSKYBool (n := n) A ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) A ρ)) :=
    toSKYBool_correct (n := n) (A := A) ρ
  simpa [LoFPrimarySKYBool.toSKYBool] using
    or_self_select
      (p := toSKYBool (n := n) A ρ)
      (b := LoFPrimary.eval (n := n) A ρ)
      hp

theorem void_left_simulated {n : Nat} (A : LoFPrimary.Expr n) (ρ : Fin n → Bool) :
    Comb.Steps (toSKYBool (n := n) (Expr.juxt Expr.void A) ρ) (toSKYBool (n := n) A ρ) := by
  show Comb.Steps
      (Comb.app (Comb.app SKYBool.ff SKYBool.ff) (toSKYBool (n := n) A ρ))
      (toSKYBool (n := n) A ρ)
  exact SKYBool.or_ff (toSKYBool (n := n) A ρ)

/-! ## Rewrite preservation: always true at the joinability / semantics level -/

theorem step_joinable_toSKYBool {n : Nat} {A B : LoFPrimary.Expr n} (h : LoFPrimary.Step A B) :
    ∀ ρ : Fin n → Bool, Joinable (toSKYBool (n := n) A ρ) (toSKYBool (n := n) B ρ) := by
  intro ρ
  refine ⟨SKYBool.ofBool (LoFPrimary.eval (n := n) A ρ), ?_, ?_⟩
  · exact toSKYBool_correct (n := n) (A := A) ρ
  · have hEqv : LoFPrimary.Eqv (n := n) A B := LoFPrimary.step_sound (n := n) h
    have hev : LoFPrimary.eval (n := n) B ρ = LoFPrimary.eval (n := n) A ρ := (hEqv ρ).symm
    have hB : Comb.Steps (toSKYBool (n := n) B ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) B ρ)) :=
      toSKYBool_correct (n := n) (A := B) ρ
    exact steps_transitive hB (Comb.Steps.of_eq (by simp [hev]))

theorem steps_joinable_toSKYBool {n : Nat} {A B : LoFPrimary.Expr n} (h : LoFPrimary.Steps A B) :
    ∀ ρ : Fin n → Bool, Joinable (toSKYBool (n := n) A ρ) (toSKYBool (n := n) B ρ) := by
  intro ρ
  refine ⟨SKYBool.ofBool (LoFPrimary.eval (n := n) A ρ), ?_, ?_⟩
  · exact toSKYBool_correct (n := n) (A := A) ρ
  · have hEqv : LoFPrimary.Eqv (n := n) A B := LoFPrimary.steps_sound (n := n) h
    have hev : LoFPrimary.eval (n := n) B ρ = LoFPrimary.eval (n := n) A ρ := (hEqv ρ).symm
    have hB : Comb.Steps (toSKYBool (n := n) B ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) B ρ)) :=
      toSKYBool_correct (n := n) (A := B) ρ
    exact steps_transitive hB (Comb.Steps.of_eq (by simp [hev]))

theorem step_boolObsEq_toSKYBool {n : Nat} {A B : LoFPrimary.Expr n} (h : LoFPrimary.Step A B) :
    ∀ ρ : Fin n → Bool, BoolObsEq (toSKYBool (n := n) A ρ) (toSKYBool (n := n) B ρ) := by
  intro ρ
  have hA : Comb.Steps (toSKYBool (n := n) A ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) A ρ)) :=
    toSKYBool_correct (n := n) (A := A) ρ
  have hB :
      Comb.Steps (toSKYBool (n := n) B ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) A ρ)) := by
    have hEqv : LoFPrimary.Eqv (n := n) A B := LoFPrimary.step_sound (n := n) h
    have hev : LoFPrimary.eval (n := n) B ρ = LoFPrimary.eval (n := n) A ρ := (hEqv ρ).symm
    have hB' :
        Comb.Steps (toSKYBool (n := n) B ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) B ρ)) :=
      toSKYBool_correct (n := n) (A := B) ρ
    exact steps_transitive hB' (Comb.Steps.of_eq (by simp [hev]))
  exact boolObsEq_of_steps_ofBool (b := LoFPrimary.eval (n := n) A ρ) hA hB

theorem steps_boolObsEq_toSKYBool {n : Nat} {A B : LoFPrimary.Expr n} (h : LoFPrimary.Steps A B) :
    ∀ ρ : Fin n → Bool, BoolObsEq (toSKYBool (n := n) A ρ) (toSKYBool (n := n) B ρ) := by
  intro ρ
  have hA : Comb.Steps (toSKYBool (n := n) A ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) A ρ)) :=
    toSKYBool_correct (n := n) (A := A) ρ
  have hB :
      Comb.Steps (toSKYBool (n := n) B ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) A ρ)) := by
    have hEqv : LoFPrimary.Eqv (n := n) A B := LoFPrimary.steps_sound (n := n) h
    have hev : LoFPrimary.eval (n := n) B ρ = LoFPrimary.eval (n := n) A ρ := (hEqv ρ).symm
    have hB' :
        Comb.Steps (toSKYBool (n := n) B ρ) (SKYBool.ofBool (LoFPrimary.eval (n := n) B ρ)) :=
      toSKYBool_correct (n := n) (A := B) ρ
    exact steps_transitive hB' (Comb.Steps.of_eq (by simp [hev]))
  exact boolObsEq_of_steps_ofBool (b := LoFPrimary.eval (n := n) A ρ) hA hB

end LoFPrimarySKYBoolStepSimulation

end Correspondence
end LoF
end HeytingLean
