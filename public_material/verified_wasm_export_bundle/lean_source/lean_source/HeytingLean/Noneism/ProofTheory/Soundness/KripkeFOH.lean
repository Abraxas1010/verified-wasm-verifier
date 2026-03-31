import HeytingLean.Noneism.Semantics.KripkeFOH

namespace HeytingLean
namespace Noneism
namespace KripkeFOH

open Syntax.Henkin

variable {W : Type} [Preorder W]
variable {σ κ D : Type}

/-!
Substitution lemmas for Henkin Kripke semantics.

These mirror the base-language results in `Noneism.ProofTheory.Soundness.KripkeFO`,
specialized to variable substitution `x ↦ var a`.
-/

theorem forces_substFormula_var_of_not_mem_boundVars
    (M : Model W σ D) (ρ : Valuation D) (η : ParamInterp κ D) (w : W) :
    ∀ (x a : Var) (φ : FormulaH σ κ),
      a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ →
        (Forces M ρ η w (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ) ↔
          Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) η w φ) := by
  intro x a φ ha
  induction φ generalizing ρ w with
  | top =>
      simp [Syntax.Henkin.substFormula, Forces]
  | bot =>
      simp [Syntax.Henkin.substFormula, Forces]
  | pred p args =>
      have hEq :
          List.map (evalTerm ρ η ∘ Syntax.Henkin.substTerm (κ := κ) x (.var a)) args =
            List.map (evalTerm (update ρ x (ρ a)) η) args := by
        apply List.map_congr_left
        intro t _ht
        cases t with
        | var z =>
            by_cases hzx : z = x <;> simp [Syntax.Henkin.substTerm, evalTerm, update, hzx]
        | param k =>
            simp [Syntax.Henkin.substTerm, evalTerm]
      simp [Syntax.Henkin.substFormula, Forces, Syntax.Henkin.substTerms, hEq]
    | eExists t =>
        cases t with
        | var z =>
            by_cases hzx : z = x <;> simp [Syntax.Henkin.substFormula, Forces, Syntax.Henkin.substTerm, evalTerm, hzx]
        | param k =>
            simp [Syntax.Henkin.substFormula, Forces, Syntax.Henkin.substTerm, evalTerm]
  | not φ ih =>
      have haφ : a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.boundVars] using ha
      constructor
      · intro h
        have hNot :
            ∀ v, w ≤ v → Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ) → False := by
          simpa [Syntax.Henkin.substFormula, Forces] using h
        intro v hwv hvφ
        have : Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ) :=
          (ih (ρ := ρ) (w := v) haφ).2 hvφ
        exact hNot v hwv this
      · intro h
        have hNot :
            ∀ v, w ≤ v → Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) η v φ → False := by
          simpa [Forces] using h
        have : Forces M ρ η w (.not (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ)) := by
          intro v hwv hvSub
          have hvφ : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) η v φ :=
            (ih (ρ := ρ) (w := v) haφ).1 hvSub
          exact hNot v hwv hvφ
        simpa [Syntax.Henkin.substFormula, Forces] using this
  | and φ ψ ihφ ihψ =>
      have ha' :
          a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ ∧
            a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.boundVars, Finset.mem_union] using ha
      simp [Syntax.Henkin.substFormula, Forces,
        ihφ (ρ := ρ) (w := w) ha'.1,
        ihψ (ρ := ρ) (w := w) ha'.2]
  | or φ ψ ihφ ihψ =>
      have ha' :
          a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ ∧
            a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.boundVars, Finset.mem_union] using ha
      simp [Syntax.Henkin.substFormula, Forces,
        ihφ (ρ := ρ) (w := w) ha'.1,
        ihψ (ρ := ρ) (w := w) ha'.2]
  | imp φ ψ ihφ ihψ =>
      have ha' :
          a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ ∧
            a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.boundVars, Finset.mem_union] using ha
      constructor
      · intro h
        have hImp :
            ∀ v, w ≤ v →
              Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ) →
                Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) ψ) := by
          simpa [Syntax.Henkin.substFormula, Forces] using h
        intro v hwv hvφ
        have hvφ' :
            Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ) :=
          (ihφ (ρ := ρ) (w := v) ha'.1).2 hvφ
        have hvψ' :
            Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) ψ) :=
          hImp v hwv hvφ'
        exact (ihψ (ρ := ρ) (w := v) ha'.2).1 hvψ'
      · intro h
        have hImp :
            ∀ v, w ≤ v →
              Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) η v φ →
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) η v ψ := by
          simpa [Forces] using h
        have : Forces M ρ η w (.imp
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) ψ)) := by
          intro v hwv hvSubφ
          have hvφ : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) η v φ :=
            (ihφ (ρ := ρ) (w := v) ha'.1).1 hvSubφ
          have hvψ : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) η v ψ := hImp v hwv hvφ
          exact (ihψ (ρ := ρ) (w := v) ha'.2).2 hvψ
        simpa [Syntax.Henkin.substFormula, Forces] using this
  | sigma z φ ih =>
      have ha' : a ≠ z ∧ a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.boundVars, Finset.mem_insert, Finset.mem_union] using ha
      have haz : a ≠ z := ha'.1
      have haφ : a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ := ha'.2
      by_cases hzx : z = x
      · subst hzx
        -- substitution stops under binder for `x`; update at `x` is overwritten
        simp [Syntax.Henkin.substFormula, Forces, HeytingLean.Noneism.KripkeFO.update_update_same]
      ·
        have hza : z ≠ a := Ne.symm haz
        have hfvt : z ∉ Syntax.Henkin.fvTerm (κ := κ) (.var a) := by
          simp [Syntax.Henkin.fvTerm, hza]
        simp [Syntax.Henkin.substFormula, hzx, hfvt, Forces]
        constructor
        · rintro ⟨d, hd⟩
          refine ⟨d, ?_⟩
          have hih := ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (w := w) haφ
          have hb :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                  ((HeytingLean.Noneism.KripkeFO.update ρ z d) a))
                η w φ := hih.1 hd
          have hza' : HeytingLean.Noneism.KripkeFO.update ρ z d a = ρ a := by
            simp [HeytingLean.Noneism.KripkeFO.update, haz]
          have hb' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (ρ a))
                η w φ := by
            simpa [hza'] using hb
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (ρ a) =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) z d := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx)
          simpa [hcomm] using hb'
        · rintro ⟨d, hd⟩
          refine ⟨d, ?_⟩
          have hih := ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (w := w) haφ
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) z d =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (ρ a) := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx).symm
          have hd' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (ρ a))
                η w φ := by
            simpa [hcomm] using hd
          have hza' : HeytingLean.Noneism.KripkeFO.update ρ z d a = ρ a := by
            simp [HeytingLean.Noneism.KripkeFO.update, haz]
          have hd'' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                  ((HeytingLean.Noneism.KripkeFO.update ρ z d) a))
                η w φ := by
            simpa [hza'] using hd'
          exact hih.2 hd''
  | pi z φ ih =>
      have ha' : a ≠ z ∧ a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.boundVars, Finset.mem_insert, Finset.mem_union] using ha
      have haz : a ≠ z := ha'.1
      have haφ : a ∉ Syntax.Henkin.boundVars (σ := σ) (κ := κ) φ := ha'.2
      by_cases hzx : z = x
      · subst hzx
        simp [Syntax.Henkin.substFormula, Forces, HeytingLean.Noneism.KripkeFO.update_update_same]
      ·
        have hza : z ≠ a := Ne.symm haz
        have hfvt : z ∉ Syntax.Henkin.fvTerm (κ := κ) (.var a) := by
          simp [Syntax.Henkin.fvTerm, hza]
        simp [Syntax.Henkin.substFormula, hzx, hfvt, Forces]
        constructor
        · intro h v hwv d
          have hih := ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (w := v) haφ
          have hb :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                  ((HeytingLean.Noneism.KripkeFO.update ρ z d) a))
                η v φ := hih.1 (h v hwv d)
          have hza' : HeytingLean.Noneism.KripkeFO.update ρ z d a = ρ a := by
            simp [HeytingLean.Noneism.KripkeFO.update, haz]
          have hb' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (ρ a))
                η v φ := by
            simpa [hza'] using hb
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (ρ a) =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) z d := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx)
          simpa [hcomm] using hb'
        · intro h v hwv d
          have hih := ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (w := v) haφ
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) z d =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (ρ a) := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx).symm
          have hd' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (ρ a))
                η v φ := by
            simpa [hcomm] using h v hwv d
          have hza' : HeytingLean.Noneism.KripkeFO.update ρ z d a = ρ a := by
            simp [HeytingLean.Noneism.KripkeFO.update, haz]
          have hd'' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                  ((HeytingLean.Noneism.KripkeFO.update ρ z d) a))
                η v φ := by
            simpa [hza'] using hd'
          exact hih.2 hd''

theorem forces_substFormula_var_of_not_mem_varsFormula
    (M : Model W σ D) (ρ : Valuation D) (η : ParamInterp κ D) (w : W)
    (x a : Var) (φ : FormulaH σ κ)
    (ha : a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ) :
    (Forces M ρ η w (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ) ↔
      Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ a)) η w φ) := by
  apply forces_substFormula_var_of_not_mem_boundVars (σ := σ) (κ := κ)
    (M := M) (ρ := ρ) (η := η) (w := w) (x := x) (a := a) (φ := φ)
  exact Syntax.Henkin.not_mem_boundVars_of_not_mem_varsFormula (σ := σ) (κ := κ) (a := a) (φ := φ) ha

end KripkeFOH
end Noneism
end HeytingLean
