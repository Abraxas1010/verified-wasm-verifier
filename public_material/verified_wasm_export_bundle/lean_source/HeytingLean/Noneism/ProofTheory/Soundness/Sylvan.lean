import HeytingLean.Noneism.ProofTheory.ND
import HeytingLean.Noneism.ProofTheory.Soundness.KripkeFO
import HeytingLean.Noneism.ProofTheory.Quantifiers.Hygiene
import HeytingLean.Noneism.Semantics.Sylvan

/-!
# Noneism.ProofTheory.Soundness.Sylvan

Soundness of the propositional ND proof system (`Noneism.ProofTheory.ND`) with respect to the
classical-style Sylvan semantics (`Noneism.Semantics.Sylvan.eval`).

This is the key step that upgrades Noneism from "semantics-only" to an internally checkable logic:

    `Derives Γ φ`  ⇒  every Sylvan model/valuation that satisfies Γ also satisfies φ.

Notes:
- This theorem is purely structural. `pred` and `eExists` remain atomic (handled by the model's
  `interp` and `existsP`).
- Once we add a hygienic binder/substitution layer for `sigma`/`pi`, we will extend the proof
  system and this soundness theorem accordingly.
-/

namespace HeytingLean
namespace Noneism

open Noneism Formula

namespace Sylvan

open Syntax

private def toKripkeModel {σ D : Type} (M : Model σ D) :
    Noneism.KripkeFO.Model Unit σ D where
  valPred _ p args := M.interp p args
  monoPred := by
    intro _ _ _ _ _ h
    simpa using h
  valEx _ d := M.existsP d
  monoEx := by
    intro _ _ _ _ h
    simpa using h

private theorem forces_toKripke_iff_eval {σ D : Type} (M : Model σ D) (ρ : Valuation D) :
    ∀ φ : Formula σ,
      (Noneism.KripkeFO.Forces (M := toKripkeModel M) ρ () φ ↔ eval M ρ φ) := by
  intro φ
  induction φ generalizing ρ with
  | top =>
      simp [Noneism.KripkeFO.Forces, eval]
  | bot =>
      simp [Noneism.KripkeFO.Forces, eval]
  | pred p args =>
      have hEvalTerm : (Noneism.KripkeFO.evalTerm ρ) = (evalTerm ρ) := by
        funext t
        cases t
        rfl
      simp [Noneism.KripkeFO.Forces, eval, toKripkeModel, hEvalTerm]
  | eExists t =>
      have hEvalTerm : Noneism.KripkeFO.evalTerm ρ t = evalTerm ρ t := by
        cases t
        rfl
      simp [Noneism.KripkeFO.Forces, eval, toKripkeModel, hEvalTerm]
  | not φ ih =>
      constructor
      · intro h hφ
        exact h () (by simp) ((ih (ρ := ρ)).2 hφ)
      · intro h v hv hvφ
        cases v
        exact h ((ih (ρ := ρ)).1 (by simpa using hvφ))
  | and φ ψ ihφ ihψ =>
      simpa [Noneism.KripkeFO.Forces, eval] using
        (and_congr (ihφ (ρ := ρ)) (ihψ (ρ := ρ)))
  | or φ ψ ihφ ihψ =>
      simpa [Noneism.KripkeFO.Forces, eval] using
        (or_congr (ihφ (ρ := ρ)) (ihψ (ρ := ρ)))
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro h hφ
        have hForcesφ : Noneism.KripkeFO.Forces (M := toKripkeModel M) ρ () φ :=
          (ihφ (ρ := ρ)).2 hφ
        have hForcesψ : Noneism.KripkeFO.Forces (M := toKripkeModel M) ρ () ψ :=
          h () (by simp) hForcesφ
        exact (ihψ (ρ := ρ)).1 hForcesψ
      · intro h v hv hvφ
        cases v
        have hEvalφ : eval M ρ φ := (ihφ (ρ := ρ)).1 (by simpa using hvφ)
        have hEvalψ : eval M ρ ψ := h hEvalφ
        exact (ihψ (ρ := ρ)).2 hEvalψ
  | sigma x φ ih =>
      constructor
      · rintro ⟨d, hd⟩
        exact ⟨d, (ih (ρ := update ρ x d)).1 (by simpa [Noneism.KripkeFO.update, update] using hd)⟩
      · rintro ⟨d, hd⟩
        exact ⟨d, (ih (ρ := update ρ x d)).2 (by simpa [Noneism.KripkeFO.update, update] using hd)⟩
  | pi x φ ih =>
      constructor
      · intro h d
        have hForces : Noneism.KripkeFO.Forces (M := toKripkeModel M)
            (Noneism.KripkeFO.update ρ x d) () φ := h () (by simp) d
        exact (ih (ρ := update ρ x d)).1 (by simpa [Noneism.KripkeFO.update, update] using hForces)
      · intro h v hv d
        cases v
        have hEval : eval M (update ρ x d) φ := h d
        exact (ih (ρ := update ρ x d)).2 (by simpa [Noneism.KripkeFO.update, update] using hEval)

/-- Semantic entailment for Sylvan models. -/
def Entails {σ D : Type} (Γ : List (Formula σ)) (φ : Formula σ) : Prop :=
  ∀ (M : Model σ D) (ρ : Valuation D), (∀ ψ ∈ Γ, eval M ρ ψ) → eval M ρ φ

theorem entails_of_mem {σ D : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (h : φ ∈ Γ) :
    Entails (σ := σ) (D := D) Γ φ := by
  intro M ρ hΓ
  exact hΓ φ h

/-! ## Small semantic helpers (valuation update + substitution) -/

theorem update_update_same {D} (ρ : Valuation D) (x : Noneism.Var) (d₁ d₂ : D) :
    update (D := D) (update ρ x d₁) x d₂ = update ρ x d₂ := by
  funext y
  by_cases hy : y = x <;> simp [update, hy]

theorem update_comm {D} (ρ : Valuation D) {x y : Noneism.Var} (dx dy : D) (h : x ≠ y) :
    update (D := D) (update ρ x dx) y dy = update (update ρ y dy) x dx := by
  funext z
  by_cases hzX : z = x
  · subst hzX
    simp [update, h]
  · by_cases hzY : z = y
    · have hyx : y ≠ x := Ne.symm h
      -- avoid `subst` here: it may eliminate the implicit binder `y`.
      simp [update, hzY, hyx]
    · simp [update, hzX, hzY]

theorem mem_fvTerms_of_mem {y : Var} {t : Term} :
    ∀ {ts : List Term}, t ∈ ts → y ∈ Syntax.fvTerm t → y ∈ Syntax.fvTerms ts
  | [], ht, _ => by cases ht
  | t0 :: ts, ht, hy => by
      rcases List.mem_cons.1 ht with rfl | ht
      · simp [Syntax.fvTerms, hy]
      · have : y ∈ Syntax.fvTerms ts := mem_fvTerms_of_mem (ts := ts) ht hy
        simpa [Syntax.fvTerms] using (Finset.mem_union.2 (Or.inr this))

theorem evalTerm_update_of_not_mem_fvTerm {D} (ρ : Valuation D) (y : Var) (d : D) :
    ∀ t : Term, y ∉ Syntax.fvTerm t → evalTerm (D := D) (update ρ y d) t = evalTerm ρ t := by
  intro t hy
  cases t with
  | var x =>
      have hyx : y ≠ x := by simpa [Syntax.fvTerm] using hy
      have hxy : x ≠ y := Ne.symm hyx
      simp [evalTerm, update, hxy]

theorem eval_update_of_not_mem_fvFormula {σ D} (M : Model σ D) (ρ : Valuation D) (y : Var) (d : D) :
    ∀ φ : Formula σ, y ∉ Syntax.fvFormula φ → (eval M (update ρ y d) φ ↔ eval M ρ φ) := by
  intro φ hy
  induction φ generalizing ρ with
  | top =>
      simp [eval]
  | bot =>
      simp [eval]
  | pred p args =>
      have hyArgs : y ∉ Syntax.fvTerms args := by simpa [Syntax.fvFormula] using hy
      have hTerm : ∀ t ∈ args, y ∉ Syntax.fvTerm t := by
        intro t ht
        intro hyT
        exact hyArgs (mem_fvTerms_of_mem (t := t) (ts := args) ht hyT)
      have hEqList :
          args.map (evalTerm (update ρ y d)) = args.map (evalTerm ρ) := by
        apply List.map_congr_left
        intro t ht
        exact evalTerm_update_of_not_mem_fvTerm (ρ := ρ) (y := y) (d := d) t (hTerm t ht)
      simp [eval, hEqList]
  | eExists t =>
      have hyT : y ∉ Syntax.fvTerm t := by simpa [Syntax.fvFormula] using hy
      have := evalTerm_update_of_not_mem_fvTerm (ρ := ρ) (y := y) (d := d) t hyT
      simp [eval, this]
  | not φ ih =>
      have hyφ : y ∉ Syntax.fvFormula φ := by simpa [Syntax.fvFormula] using hy
      have := ih (ρ := ρ) hyφ
      simp [eval, this]
  | and φ ψ ihφ ihψ =>
      have hy' : y ∉ Syntax.fvFormula φ ∧ y ∉ Syntax.fvFormula ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      have hφ := ihφ (ρ := ρ) hy'.1
      have hψ := ihψ (ρ := ρ) hy'.2
      simp [eval, hφ, hψ]
  | or φ ψ ihφ ihψ =>
      have hy' : y ∉ Syntax.fvFormula φ ∧ y ∉ Syntax.fvFormula ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      have hφ := ihφ (ρ := ρ) hy'.1
      have hψ := ihψ (ρ := ρ) hy'.2
      simp [eval, hφ, hψ]
  | imp φ ψ ihφ ihψ =>
      have hy' : y ∉ Syntax.fvFormula φ ∧ y ∉ Syntax.fvFormula ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      have hφ := ihφ (ρ := ρ) hy'.1
      have hψ := ihψ (ρ := ρ) hy'.2
      constructor
      · intro hImp hφ0
        -- transport `hφ0` into the updated valuation, apply `hImp`, then transport back.
        exact hψ.1 (hImp (hφ.2 hφ0))
      · intro hImp hφu
        exact hψ.2 (hImp (hφ.1 hφu))
  | sigma x φ ih =>
      -- `fvFormula (sigma x φ) = (fvFormula φ).erase x`
      by_cases hyx : y = x
      · subst hyx
        -- updating the bound variable is overwritten by the binder
        simp [eval, update_update_same]
      · have hyφ : y ∉ Syntax.fvFormula φ := by
          -- from `y ∉ erase x (fvFormula φ)` and `y ≠ x`, conclude `y ∉ fvFormula φ`
          intro hy'
          exact hy (by
            exact (Finset.mem_erase.2 ⟨hyx, hy'⟩))
        constructor <;> intro h
        · rcases h with ⟨d', hd'⟩
          refine ⟨d', ?_⟩
          -- commute updates then apply IH
          have hcomm :
              update (update ρ y d) x d' = update (update ρ x d') y d := by
            simpa using (update_comm (ρ := ρ) (x := y) (y := x) (dx := d) (dy := d') hyx)
          have hd'' : eval M (update (update ρ x d') y d) φ := by
            simpa [hcomm] using hd'
          exact (ih (ρ := update ρ x d') hyφ).1 hd''
        · rcases h with ⟨d', hd'⟩
          refine ⟨d', ?_⟩
          have hd'' : eval M (update (update ρ x d') y d) φ :=
            (ih (ρ := update ρ x d') hyφ).2 hd'
          have hcomm :
              update (update ρ y d) x d' = update (update ρ x d') y d := by
            simpa using (update_comm (ρ := ρ) (x := y) (y := x) (dx := d) (dy := d') hyx)
          simpa [hcomm] using hd''
  | pi x φ ih =>
      by_cases hyx : y = x
      · subst hyx
        simp [eval, update_update_same]
      · have hyφ : y ∉ Syntax.fvFormula φ := by
          intro hy'
          exact hy (Finset.mem_erase.2 ⟨hyx, hy'⟩)
        constructor <;> intro h d'
        · have hcomm :
              update (update ρ y d) x d' = update (update ρ x d') y d := by
            simpa using (update_comm (ρ := ρ) (x := y) (y := x) (dx := d) (dy := d') hyx)
          have hd'' : eval M (update (update ρ x d') y d) φ := by
            simpa [hcomm] using h d'
          exact (ih (ρ := update ρ x d') hyφ).1 hd''
        · have hd'' : eval M (update (update ρ x d') y d) φ :=
            (ih (ρ := update ρ x d') hyφ).2 (h d')
          have hcomm :
              update (update ρ y d) x d' = update (update ρ x d') y d := by
            simpa using (update_comm (ρ := ρ) (x := y) (y := x) (dx := d) (dy := d') hyx)
          simpa [hcomm] using hd''

theorem not_mem_fvFormula_of_not_mem_fvContext {σ : Type} (a : Var) :
    ∀ {Γ : List (Formula σ)} {ψ : Formula σ},
      a ∉ ND.fvContext (σ := σ) Γ → ψ ∈ Γ → a ∉ Syntax.fvFormula ψ := by
  intro Γ ψ hctx hmem
  exact Syntax.not_mem_fvFormula_of_not_mem_fvContext (σ := σ) (Γ := Γ) (a := a) hctx hmem

theorem eval_update_of_not_mem_varsFormula {σ D} (M : Model σ D) (ρ : Valuation D) (y : Var) (d : D) :
    ∀ φ : Formula σ, y ∉ Syntax.varsFormula φ → (eval M (update ρ y d) φ ↔ eval M ρ φ) := by
  intro φ hy
  induction φ generalizing ρ with
  | top =>
      simp [eval]
  | bot =>
      simp [eval]
  | pred p args =>
      -- `varsFormula` for preds is `fvTerms`, so we can reuse the fv-lemma.
      have : y ∉ Syntax.fvFormula (.pred p args : Formula σ) := by
        simpa [Syntax.varsFormula, Syntax.fvFormula] using hy
      simpa using (eval_update_of_not_mem_fvFormula (M := M) (ρ := ρ) (y := y) (d := d) (.pred p args) this)
  | eExists t =>
      have : y ∉ Syntax.fvFormula (.eExists t : Formula σ) := by
        simpa [Syntax.varsFormula, Syntax.fvFormula] using hy
      simpa using (eval_update_of_not_mem_fvFormula (M := M) (ρ := ρ) (y := y) (d := d) (.eExists t) this)
  | not φ ih =>
      have hyφ : y ∉ Syntax.varsFormula φ := by simpa [Syntax.varsFormula] using hy
      have := ih (ρ := ρ) hyφ
      simp [eval, this]
  | and φ ψ ihφ ihψ =>
      have hy' : y ∉ Syntax.varsFormula φ ∧ y ∉ Syntax.varsFormula ψ := by
        simpa [Syntax.varsFormula, Finset.mem_union] using hy
      have hφ := ihφ (ρ := ρ) hy'.1
      have hψ := ihψ (ρ := ρ) hy'.2
      simp [eval, hφ, hψ]
  | or φ ψ ihφ ihψ =>
      have hy' : y ∉ Syntax.varsFormula φ ∧ y ∉ Syntax.varsFormula ψ := by
        simpa [Syntax.varsFormula, Finset.mem_union] using hy
      have hφ := ihφ (ρ := ρ) hy'.1
      have hψ := ihψ (ρ := ρ) hy'.2
      simp [eval, hφ, hψ]
  | imp φ ψ ihφ ihψ =>
      have hy' : y ∉ Syntax.varsFormula φ ∧ y ∉ Syntax.varsFormula ψ := by
        simpa [Syntax.varsFormula, Finset.mem_union] using hy
      have hφ := ihφ (ρ := ρ) hy'.1
      have hψ := ihψ (ρ := ρ) hy'.2
      constructor
      · intro hImp hφ0
        exact hψ.1 (hImp (hφ.2 hφ0))
      · intro hImp hφu
        exact hψ.2 (hImp (hφ.1 hφu))
  | sigma x φ ih =>
      have hy' : y ≠ x ∧ y ∉ Syntax.varsFormula φ := by
        simpa [Syntax.varsFormula, Finset.mem_insert, Finset.mem_union] using hy
      constructor <;> intro h
      · rcases h with ⟨d', hd'⟩
        refine ⟨d', ?_⟩
        -- commute updates (`y ≠ x`) then apply IH to the body under `update ρ x d'`
        have hcomm : update (update ρ y d) x d' = update (update ρ x d') y d := by
          simpa using (update_comm (ρ := ρ) (x := y) (y := x) (dx := d) (dy := d') hy'.1)
        have hd'' : eval M (update (update ρ x d') y d) φ := by
          simpa [hcomm] using hd'
        exact (ih (ρ := update ρ x d') hy'.2).1 hd''
      · rcases h with ⟨d', hd'⟩
        refine ⟨d', ?_⟩
        have hd'' : eval M (update (update ρ x d') y d) φ :=
          (ih (ρ := update ρ x d') hy'.2).2 hd'
        have hcomm : update (update ρ y d) x d' = update (update ρ x d') y d := by
          simpa using (update_comm (ρ := ρ) (x := y) (y := x) (dx := d) (dy := d') hy'.1)
        simpa [hcomm] using hd''
  | pi x φ ih =>
      have hy' : y ≠ x ∧ y ∉ Syntax.varsFormula φ := by
        simpa [Syntax.varsFormula, Finset.mem_insert, Finset.mem_union] using hy
      constructor <;> intro h d'
      · have hd'' : eval M (update (update ρ x d') y d) φ := by
          have hcomm : update (update ρ y d) x d' = update (update ρ x d') y d := by
            simpa using (update_comm (ρ := ρ) (x := y) (y := x) (dx := d) (dy := d') hy'.1)
          simpa [hcomm] using h d'
        exact (ih (ρ := update ρ x d') hy'.2).1 hd''
      · have hd'' : eval M (update (update ρ x d') y d) φ :=
          (ih (ρ := update ρ x d') hy'.2).2 (h d')
        have hcomm : update (update ρ y d) x d' = update (update ρ x d') y d := by
          simpa using (update_comm (ρ := ρ) (x := y) (y := x) (dx := d) (dy := d') hy'.1)
        simpa [hcomm] using hd''

theorem eval_substFormula_var_of_not_mem_varsFormula {σ D} (M : Model σ D) (ρ : Valuation D)
    (x a : Var) :
    ∀ φ : Formula σ,
      a ∉ Syntax.varsFormula φ →
      (eval M ρ (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
        eval M (update ρ x (ρ a)) φ) := by
  intro φ ha
  induction φ generalizing ρ with
  | top =>
      simp [Syntax.substFormula, eval]
  | bot =>
      simp [Syntax.substFormula, eval]
  | pred p args =>
      have hEq :
          List.map (evalTerm ρ ∘ Syntax.substTerm x (.var a)) args =
            List.map (evalTerm (update ρ x (ρ a))) args := by
        apply List.map_congr_left
        intro t ht
        cases t with
        | var z =>
            by_cases hzx : z = x <;> simp [Syntax.substTerm, evalTerm, update, hzx]
      simp [Syntax.substFormula, eval, Syntax.substTerms, hEq]
  | eExists t =>
      cases t with
      | var z =>
          by_cases hzx : z = x <;> simp [Syntax.substFormula, eval, Syntax.substTerm, evalTerm, update, hzx]
  | not φ ih =>
      have haφ : a ∉ Syntax.varsFormula φ := by simpa [Syntax.varsFormula] using ha
      simp [Syntax.substFormula, eval, ih (ρ := ρ) haφ]
  | and φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.varsFormula φ ∧ a ∉ Syntax.varsFormula ψ := by
        simpa [Syntax.varsFormula, Finset.mem_union] using ha
      simp [Syntax.substFormula, eval, ihφ (ρ := ρ) ha'.1, ihψ (ρ := ρ) ha'.2]
  | or φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.varsFormula φ ∧ a ∉ Syntax.varsFormula ψ := by
        simpa [Syntax.varsFormula, Finset.mem_union] using ha
      simp [Syntax.substFormula, eval, ihφ (ρ := ρ) ha'.1, ihψ (ρ := ρ) ha'.2]
  | imp φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.varsFormula φ ∧ a ∉ Syntax.varsFormula ψ := by
        simpa [Syntax.varsFormula, Finset.mem_union] using ha
      simp [Syntax.substFormula, eval, ihφ (ρ := ρ) ha'.1, ihψ (ρ := ρ) ha'.2]
  | sigma z φ ih =>
      have ha' : a ≠ z ∧ a ∉ Syntax.varsFormula φ := by
        simpa [Syntax.varsFormula, Finset.mem_insert, Finset.mem_union] using ha
      have haz : a ≠ z := ha'.1
      have haφ : a ∉ Syntax.varsFormula φ := ha'.2
      by_cases hzx : z = x
      · subst hzx
        -- substitution stops under binder for `x`; update at `x` is overwritten
        simp [Syntax.substFormula, eval, update_update_same]
      · -- no alpha-renaming can occur because `z ≠ a`
        have hza : z ≠ a := Ne.symm haz
        have hfvt : z ∉ Syntax.fvTerm (.var a) := by
          simp [Syntax.fvTerm, hza]
        simp [Syntax.substFormula, eval, hzx, hfvt]
        constructor
        · rintro ⟨d', hd'⟩
          refine ⟨d', ?_⟩
          have hih := ih (ρ := update ρ z d') haφ
          have hb : eval M (update (update ρ z d') x ((update ρ z d') a)) φ :=
            (hih.1 hd')
          have haVal : (update ρ z d') a = ρ a := by
            -- `update` needs the hypothesis in the `a ≠ z` orientation.
            simp [update, haz]
          have hb' : eval M (update (update ρ z d') x (ρ a)) φ := by
            simpa [haVal] using hb
          have hcomm :
              update (update ρ z d') x (ρ a) = update (update ρ x (ρ a)) z d' := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d') (dy := ρ a) hzx)
          simpa [hcomm] using hb'
        · rintro ⟨d', hd'⟩
          refine ⟨d', ?_⟩
          have hih := ih (ρ := update ρ z d') haφ
          have hcomm :
              update (update ρ z d') x (ρ a) = update (update ρ x (ρ a)) z d' := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d') (dy := ρ a) hzx)
          have hb' : eval M (update (update ρ z d') x (ρ a)) φ := by
            simpa [hcomm] using hd'
          have haVal : (update ρ z d') a = ρ a := by
            simp [update, haz]
          have hb : eval M (update (update ρ z d') x ((update ρ z d') a)) φ := by
            simpa [haVal] using hb'
          exact (hih.2 hb)

  | pi z φ ih =>
      have ha' : a ≠ z ∧ a ∉ Syntax.varsFormula φ := by
        simpa [Syntax.varsFormula, Finset.mem_insert, Finset.mem_union] using ha
      have haz : a ≠ z := ha'.1
      have haφ : a ∉ Syntax.varsFormula φ := ha'.2
      by_cases hzx : z = x
      · subst hzx
        simp [Syntax.substFormula, eval, update_update_same]
      · have : z ∉ Syntax.fvTerm (.var a) := by
          have hza : z ≠ a := Ne.symm haz
          simp [Syntax.fvTerm, hza]
        simp [Syntax.substFormula, eval, hzx, this]
        constructor
        · intro h d'
          have hza : z ≠ a := Ne.symm haz
          have hih := ih (ρ := update ρ z d') haφ
          have hb : eval M (update (update ρ z d') x ((update ρ z d') a)) φ :=
            (hih.1 (h d'))
          have haVal : (update ρ z d') a = ρ a := by
            simp [update, haz]
          have hb' : eval M (update (update ρ z d') x (ρ a)) φ := by
            simpa [haVal] using hb
          have hcomm :
              update (update ρ z d') x (ρ a) = update (update ρ x (ρ a)) z d' := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d') (dy := ρ a) hzx)
          simpa [hcomm] using hb'
        · intro h d'
          have hza : z ≠ a := Ne.symm haz
          have hih := ih (ρ := update ρ z d') haφ
          have hcomm :
              update (update ρ z d') x (ρ a) = update (update ρ x (ρ a)) z d' := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d') (dy := ρ a) hzx)
          have hb' : eval M (update (update ρ z d') x (ρ a)) φ := by
            simpa [hcomm] using h d'
          have haVal : (update ρ z d') a = ρ a := by
            simp [update, haz]
          have hb : eval M (update (update ρ z d') x ((update ρ z d') a)) φ := by
            simpa [haVal] using hb'
          exact (hih.2 hb)

theorem eval_substFormula_var_of_not_mem_boundVars {σ D} (M : Model σ D) (ρ : Valuation D)
    (x a : Var) (φ : Formula σ) (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    (eval M ρ (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
      eval M (update ρ x (ρ a)) φ) := by
  let MK : Noneism.KripkeFO.Model Unit σ D := toKripkeModel M
  have hk :
      (Noneism.KripkeFO.Forces (M := MK) ρ () (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
        Noneism.KripkeFO.Forces (M := MK) (Noneism.KripkeFO.update ρ x (ρ a)) () φ) :=
    Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars (σ := σ)
      (M := MK) (ρ := ρ) (w := ()) x a φ ha
  have hL :
      (Noneism.KripkeFO.Forces (M := MK) ρ () (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
        eval M ρ (Syntax.substFormula (σ := σ) x (.var a) φ)) := by
    simpa [MK] using
      (forces_toKripke_iff_eval (M := M) (ρ := ρ)
        (φ := Syntax.substFormula (σ := σ) x (.var a) φ))
  have hR :
      (Noneism.KripkeFO.Forces (M := MK) (Noneism.KripkeFO.update ρ x (ρ a)) () φ ↔
        eval M (update ρ x (ρ a)) φ) := by
    simpa [MK, Noneism.KripkeFO.update, update] using
      (forces_toKripke_iff_eval (M := M)
        (ρ := Noneism.KripkeFO.update ρ x (ρ a)) (φ := φ))
  exact hL.symm.trans (hk.trans hR)

theorem eval_substFormula_var {σ D} (M : Model σ D) (ρ : Valuation D)
    (x a : Var) (φ : Formula σ) :
    (eval M ρ (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
      eval M (update ρ x (ρ a)) φ) := by
  let MK : Noneism.KripkeFO.Model Unit σ D := toKripkeModel M
  have hk :
      (Noneism.KripkeFO.Forces (M := MK) ρ () (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
        Noneism.KripkeFO.Forces (M := MK) (Noneism.KripkeFO.update ρ x (ρ a)) () φ) :=
    Noneism.KripkeFO.forces_substFormula_var (σ := σ)
      (M := MK) (ρ := ρ) (w := ()) x a φ
  have hL :
      (Noneism.KripkeFO.Forces (M := MK) ρ () (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
        eval M ρ (Syntax.substFormula (σ := σ) x (.var a) φ)) := by
    simpa [MK] using
      (forces_toKripke_iff_eval (M := M) (ρ := ρ)
        (φ := Syntax.substFormula (σ := σ) x (.var a) φ))
  have hR :
      (Noneism.KripkeFO.Forces (M := MK) (Noneism.KripkeFO.update ρ x (ρ a)) () φ ↔
        eval M (update ρ x (ρ a)) φ) := by
    simpa [MK, Noneism.KripkeFO.update, update] using
      (forces_toKripke_iff_eval (M := M)
        (ρ := Noneism.KripkeFO.update ρ x (ρ a)) (φ := φ))
  exact hL.symm.trans (hk.trans hR)

theorem soundness {σ D : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ → Entails (σ := σ) (D := D) Γ φ := by
  intro hDer
  induction hDer with
  | hyp hmem =>
      exact entails_of_mem (σ := σ) (D := D) hmem
  | topI =>
      intro M ρ _; simp [eval]
  | botE h ih =>
      rename_i Γ φ
      intro M ρ hΓ
      have hbot : eval M ρ (.bot : Formula σ) := ih M ρ hΓ
      have hfalse : False := by
        -- `eval` at `.bot` reduces definitionally to `False`.
        exact hbot
      exact False.elim hfalse
  | andI h1 h2 ih1 ih2 =>
      rename_i Γ φ ψ
      intro M ρ hΓ
      have hφ : eval M ρ φ := ih1 M ρ hΓ
      have hψ : eval M ρ ψ := ih2 M ρ hΓ
      exact (by simp [eval, hφ, hψ])
  | andEL h ih =>
      rename_i Γ φ ψ
      intro M ρ hΓ
      have hAnd : eval M ρ (.and φ ψ) := ih M ρ hΓ
      have : eval M ρ φ ∧ eval M ρ ψ := by simpa [eval] using hAnd
      exact this.1
  | andER h ih =>
      rename_i Γ φ ψ
      intro M ρ hΓ
      have hAnd : eval M ρ (.and φ ψ) := ih M ρ hΓ
      have : eval M ρ φ ∧ eval M ρ ψ := by simpa [eval] using hAnd
      exact this.2
  | orIL h ih =>
      rename_i Γ φ ψ
      intro M ρ hΓ
      have hφ : eval M ρ φ := ih M ρ hΓ
      exact (by simp [eval, hφ])
  | orIR h ih =>
      rename_i Γ φ ψ
      intro M ρ hΓ
      have hψ : eval M ρ ψ := ih M ρ hΓ
      exact (by simp [eval, hψ])
  | orE h h1 h2 ih ih1 ih2 =>
      rename_i Γ φ ψ χ
      intro M ρ hΓ
      have hOr : eval M ρ (.or φ ψ) := ih M ρ hΓ
      have hOr' : eval M ρ φ ∨ eval M ρ ψ := by simpa [eval] using hOr
      cases hOr' with
      | inl hφ =>
          have hΓ' : ∀ θ ∈ (φ :: Γ), eval M ρ θ := by
            intro θ hθ
            rcases List.mem_cons.1 hθ with rfl | hθ
            · exact hφ
            · exact hΓ θ hθ
          exact ih1 M ρ hΓ'
      | inr hψ =>
          have hΓ' : ∀ θ ∈ (ψ :: Γ), eval M ρ θ := by
            intro θ hθ
            rcases List.mem_cons.1 hθ with rfl | hθ
            · exact hψ
            · exact hΓ θ hθ
          exact ih2 M ρ hΓ'
  | impI h ih =>
      rename_i Γ φ ψ
      intro M ρ hΓ hφ
      -- `eval` of implication is implication in Prop.
      have hΓ' : ∀ θ ∈ (φ :: Γ), eval M ρ θ := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hφ
        · exact hΓ θ hθ
      have hψ : eval M ρ ψ := ih M ρ hΓ'
      simpa [eval] using hψ
  | impE h1 h2 ih1 ih2 =>
      rename_i Γ φ ψ
      intro M ρ hΓ
      have himp : eval M ρ (.imp φ ψ) := ih1 M ρ hΓ
      have hφ : eval M ρ φ := ih2 M ρ hΓ
      have himp' : eval M ρ φ → eval M ρ ψ := by simpa [eval] using himp
      exact himp' hφ
  | notI h ih =>
      rename_i Γ φ
      intro M ρ hΓ hφ
      have hΓ' : ∀ θ ∈ (φ :: Γ), eval M ρ θ := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hφ
        · exact hΓ θ hθ
      have hbot : eval M ρ (.bot : Formula σ) := ih M ρ hΓ'
      -- `eval` at `.bot` reduces definitionally to `False`.
      exact hbot
  | notE h1 h2 ih1 ih2 =>
      rename_i Γ φ
      intro M ρ hΓ
      have hnot : eval M ρ (.not φ) := ih1 M ρ hΓ
      have hφ : eval M ρ φ := ih2 M ρ hΓ
      have hnot' : ¬ eval M ρ φ := by simpa [eval] using hnot
      have : False := hnot' hφ
      exact this
  | wk h hsub ih =>
      intro M ρ hΓ
      exact ih M ρ (by
        intro θ hθ
        exact hΓ θ (hsub hθ))
  | piI ha hvars h ih =>
      rename_i Γ x a φ
      intro M ρ hΓ d
      -- show `∀ d, eval M (update ρ x d) φ`
      -- pick a valuation that maps the eigenvariable `a` to `d`
      let ρa : Valuation D := update ρ a d
      have hΓa : ∀ ψ ∈ Γ, eval M ρa ψ := by
        intro ψ hψ
        have hfv : a ∉ Syntax.fvFormula ψ :=
          not_mem_fvFormula_of_not_mem_fvContext (σ := σ) a (Γ := Γ) (ψ := ψ) ha hψ
        have hEq : eval M (update ρ a d) ψ ↔ eval M ρ ψ :=
          eval_update_of_not_mem_fvFormula (M := M) (ρ := ρ) (y := a) (d := d) ψ hfv
        exact hEq.2 (hΓ ψ hψ)
      have hSub : eval M ρa (Syntax.substFormula (σ := σ) x (.var a) φ) := ih M ρa hΓa
      have hφd : eval M (update ρa x (ρa a)) φ := by
        -- substitution lemma (no alpha renaming due to `a ∉ varsFormula φ`)
        have := (eval_substFormula_var_of_not_mem_varsFormula (M := M) (ρ := ρa) (x := x) (a := a) φ hvars).1 hSub
        simpa [ρa, update_self] using this
      -- Now move from the `ρa`-world back to the original valuation.
      have htmp : eval M (update (update ρ a d) x d) φ := by
        -- `ρa a = d`, so `update ρa x (ρa a) = update (update ρ a d) x d`.
        simpa [ρa, update] using hφd
      by_cases hax : a = x
      · subst hax
        simpa [update_update_same] using htmp
      · -- commute the updates and drop the irrelevant `a`-update (since `a` does not occur in `φ`).
        have hcomm : update (update ρ a d) x d = update (update ρ x d) a d := by
          simpa using (update_comm (ρ := ρ) (x := a) (y := x) (dx := d) (dy := d) hax)
        have htmp' : eval M (update (update ρ x d) a d) φ := by
          simpa [hcomm] using htmp
        have hdrop : eval M (update (update ρ x d) a d) φ ↔ eval M (update ρ x d) φ :=
          eval_update_of_not_mem_varsFormula (M := M) (ρ := update ρ x d) (y := a) (d := d) φ hvars
        exact hdrop.1 htmp'
  | piE h ih =>
      rename_i Γ x a φ
      intro M ρ hΓ
      have hPi : eval M ρ (.pi x φ) := ih M ρ hΓ
      -- instantiate at `a` (in semantics: choose `d := ρ a`)
      have hInst : eval M (update ρ x (ρ a)) φ := by
        have := hPi (ρ a)
        simpa [eval] using this
      -- relate to the syntactic substitution instance
      have := (eval_substFormula_var (M := M) (ρ := ρ) (x := x) (a := a) φ).2 hInst
      exact this
  | sigmaI h ih =>
      rename_i Γ x a φ
      intro M ρ hΓ
      have hSub : eval M ρ (Syntax.substFormula (σ := σ) x (.var a) φ) := ih M ρ hΓ
      have hφ : eval M (update ρ x (ρ a)) φ :=
        (eval_substFormula_var (M := M) (ρ := ρ) (x := x) (a := a) φ).1 hSub
      -- witness is `ρ a`
      refine ⟨ρ a, ?_⟩
      simpa [eval] using hφ
  | sigmaE hσ ha hvars hχ hder ihσ ihder =>
      rename_i Γ x a φ χ
      intro M ρ hΓ
      have hEx : eval M ρ (.sigma x φ) := ihσ M ρ hΓ
      rcases hEx with ⟨d, hd⟩
      -- Evaluate the substituted assumption under a valuation mapping `a ↦ d`.
      let ρa : Valuation D := update ρ a d
      have hΓa : ∀ ψ ∈ Γ, eval M ρa ψ := by
        intro ψ hψ
        have hfv : a ∉ Syntax.fvFormula ψ :=
          not_mem_fvFormula_of_not_mem_fvContext (σ := σ) a (Γ := Γ) (ψ := ψ) ha hψ
        have hEq : eval M ρa ψ ↔ eval M ρ ψ :=
          eval_update_of_not_mem_fvFormula (M := M) (ρ := ρ) (y := a) (d := d) ψ hfv
        exact hEq.2 (hΓ ψ hψ)
      have hAssm : eval M ρa (Syntax.substFormula (σ := σ) x (.var a) φ) := by
        -- substitution lemma (no alpha due to `a ∉ varsFormula φ`)
        have hφ : eval M (update ρa x (ρa a)) φ := by
          -- `hd : eval M (update ρ x d) φ`. Relate it to `update ρa x (ρa a)`.
          -- The extra update at `a` commutes with `x` and is semantically irrelevant since
          -- `a ∉ varsFormula φ`.
          by_cases hax : a = x
          · subst hax
            -- `update ρa x (ρa a) = update (update ρ x d) x d = update ρ x d`.
            simpa [ρa, update_update_same, update_self] using hd
          · have hcomm : update (update ρ a d) x d = update (update ρ x d) a d := by
              simpa using (update_comm (ρ := ρ) (x := a) (y := x) (dx := d) (dy := d) hax)
            have hdrop :
                eval M (update (update ρ x d) a d) φ ↔ eval M (update ρ x d) φ :=
              eval_update_of_not_mem_varsFormula (M := M) (ρ := update ρ x d) (y := a) (d := d) φ hvars
            have htmp : eval M (update (update ρ a d) x d) φ := by
              have : eval M (update (update ρ x d) a d) φ := hdrop.2 hd
              simpa [hcomm] using this
            -- `update ρa x (ρa a) = update (update ρ a d) x d`.
            simpa [ρa, update_self] using htmp
        exact (eval_substFormula_var_of_not_mem_varsFormula (M := M) (ρ := ρa) (x := x) (a := a) φ hvars).2 hφ
      have hCtx : ∀ θ ∈ (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ), eval M ρa θ := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hAssm
        · exact hΓa θ hθ
      have hχa : eval M ρa χ := ihder M ρa hCtx
      -- Drop the irrelevant update at `a` (since `a` is not free in `χ`).
      have hdrop : eval M ρa χ ↔ eval M ρ χ :=
        (eval_update_of_not_mem_fvFormula (M := M) (ρ := ρ) (y := a) (d := d) χ hχ)
      exact hdrop.1 hχa

end Sylvan

end Noneism
end HeytingLean
