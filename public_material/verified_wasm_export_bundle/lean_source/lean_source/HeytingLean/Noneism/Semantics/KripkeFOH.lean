import Mathlib.Order.Basic
import HeytingLean.Noneism.Syntax.Henkin
import HeytingLean.Noneism.Semantics.KripkeFO

namespace HeytingLean
namespace Noneism
namespace KripkeFOH

open Syntax.Henkin

/-- Variable assignment for Henkin formulas. -/
abbrev Valuation (D : Type) := Var → D

/-- Interpretation of Henkin parameters into the semantic domain. -/
abbrev ParamInterp (κ : Type) (D : Type) := κ → D

/-- Update a variable valuation at `x`. -/
def update {D : Type} (ρ : Valuation D) (x : Var) (d : D) : Valuation D :=
  fun y => if y = x then d else ρ y

@[simp] theorem update_self {D : Type} (ρ : Valuation D) (x : Var) (d : D) :
    update ρ x d x = d := by
  simp [update]

@[simp] theorem update_other {D : Type}
    (ρ : Valuation D) (x y : Var) (d : D) (h : y ≠ x) :
    update ρ x d y = ρ y := by
  simp [update, h]

theorem update_update_same {D : Type} (ρ : Valuation D) (x : Var) (d₁ d₂ : D) :
    update (update ρ x d₁) x d₂ = update ρ x d₂ := by
  funext y
  by_cases hy : y = x <;> simp [update, hy]

theorem update_comm {D : Type}
    (ρ : Valuation D) {x y : Var} (dx dy : D) (h : x ≠ y) :
    update (update ρ x dx) y dy = update (update ρ y dy) x dx := by
  funext z
  by_cases hzx : z = x
  · subst hzx
    simp [update, h]
  · by_cases hzy : z = y
    · subst hzy
      simp [update, hzx]
    · simp [update, hzx, hzy]

/-- Evaluate a Henkin term under variable and parameter interpretations. -/
def evalTerm {κ D : Type} (ρ : Valuation D) (η : ParamInterp κ D) : TermH κ → D
  | .var x => ρ x
  | .param k => η k

/-- Kripke model for Henkin formulas over constant domain `D`. -/
structure Model (W : Type) (σ : Type) (D : Type) [Preorder W] where
  /-- Atomic valuation for predicate symbols. Monotone over worlds. -/
  valPred : W → σ → List D → Prop
  monoPred : ∀ {w v : W}, w ≤ v → ∀ p args, valPred w p args → valPred v p args
  /-- Atomic valuation for `eExists`. Monotone over worlds. -/
  valEx : W → D → Prop
  monoEx : ∀ {w v : W}, w ≤ v → ∀ d, valEx w d → valEx v d

/-- Forcing relation for Henkin formulas. -/
def Forces {W : Type} [Preorder W] {σ κ D : Type}
    (M : Model W σ D) (ρ : Valuation D) (η : ParamInterp κ D) :
    W → FormulaH σ κ → Prop
  | _, .top => True
  | _, .bot => False
  | w, .pred p args => M.valPred w p (args.map (evalTerm ρ η))
  | w, .eExists t => M.valEx w (evalTerm ρ η t)
  | w, .not φ => ∀ v, w ≤ v → Forces M ρ η v φ → False
  | w, .and φ ψ => Forces M ρ η w φ ∧ Forces M ρ η w ψ
  | w, .or φ ψ => Forces M ρ η w φ ∨ Forces M ρ η w ψ
  | w, .imp φ ψ => ∀ v, w ≤ v → Forces M ρ η v φ → Forces M ρ η v ψ
  | w, .sigma x φ => ∃ d : D, Forces M (update ρ x d) η w φ
  | w, .pi x φ => ∀ v, w ≤ v → ∀ d : D, Forces M (update ρ x d) η v φ

/-- Semantic entailment for Henkin formulas. -/
def Entails {σ κ : Type} (Γ : List (FormulaH σ κ)) (φ : FormulaH σ κ) : Prop :=
  ∀ (W : Type) [Preorder W] (D : Type) (M : Model W σ D)
    (ρ : Valuation D) (η : ParamInterp κ D) (w : W),
    (∀ ψ ∈ Γ, Forces M ρ η w ψ) → Forces M ρ η w φ

/-! ## Bridge from base FO semantics (`KripkeFO`) via `liftFormula` -/

/-- Forget parameters in a base FO model to view it as a Henkin model. -/
def liftModel {W : Type} [Preorder W] {σ D : Type}
    (M : HeytingLean.Noneism.KripkeFO.Model W σ D) :
    Model W σ D where
  valPred := M.valPred
  monoPred := by
    intro w v hwv p args h
    exact M.monoPred hwv p args h
  valEx := M.valEx
  monoEx := by
    intro w v hwv d h
    exact M.monoEx hwv d h

/-- Forget parameters from a Henkin model to recover a base FO model. -/
def lowerModel {W : Type} [Preorder W] {σ D : Type}
    (MH : Model W σ D) :
    HeytingLean.Noneism.KripkeFO.Model W σ D where
  valPred := MH.valPred
  monoPred := by
    intro w v hwv p args h
    exact MH.monoPred hwv p args h
  valEx := MH.valEx
  monoEx := by
    intro w v hwv d h
    exact MH.monoEx hwv d h

@[simp] theorem liftModel_lowerModel
    {W : Type} [Preorder W] {σ D : Type}
    (MH : Model W σ D) :
    liftModel (M := lowerModel MH) = MH := by
  cases MH
  rfl

@[simp] theorem evalTerm_liftTerm
    {κ D : Type}
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
    (η : ParamInterp κ D)
    (t : Term) :
    evalTerm ρ η (liftTerm (κ := κ) t) =
      HeytingLean.Noneism.KripkeFO.evalTerm ρ t := by
  cases t with
  | var x =>
      simp [liftTerm, evalTerm, HeytingLean.Noneism.KripkeFO.evalTerm]

@[simp] theorem map_evalTerm_liftTerm
    {κ D : Type}
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
    (η : ParamInterp κ D)
    (args : List Term) :
    List.map (evalTerm ρ η ∘ liftTerm (κ := κ)) args =
      List.map (HeytingLean.Noneism.KripkeFO.evalTerm ρ) args := by
  induction args with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [Function.comp, evalTerm_liftTerm, ih]

@[simp] theorem update_eq_base
    {D : Type}
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
    (x : Var) (d : D) :
    update ρ x d = HeytingLean.Noneism.KripkeFO.update ρ x d := by
  funext y
  simp [update, HeytingLean.Noneism.KripkeFO.update]

/--
`liftFormula` is semantics-preserving between base FO Kripke semantics and Henkin semantics.

This is the key transfer lemma for using Henkin-layer constructions to produce
countermodels for base formulas.
-/
theorem forces_liftFormula_iff
    {W : Type} [Preorder W] {σ κ D : Type}
    (M : HeytingLean.Noneism.KripkeFO.Model W σ D)
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
    (η : ParamInterp κ D) :
    ∀ (w : W) (φ : Formula σ),
      Forces (liftModel M) ρ η w (liftFormula (σ := σ) (κ := κ) φ) ↔
        HeytingLean.Noneism.KripkeFO.Forces M ρ w φ := by
  intro w φ
  induction φ generalizing ρ w with
  | top =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula]
  | bot =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula]
  | pred p args =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula, map_evalTerm_liftTerm, liftModel]
  | eExists t =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula, evalTerm_liftTerm, liftModel]
  | not φ ih =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula, ih]
  | and φ ψ ihφ ihψ =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula, ihφ, ihψ]
  | sigma x φ ih =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula, ih, update_eq_base]
  | pi x φ ih =>
      simp [Forces, HeytingLean.Noneism.KripkeFO.Forces, liftFormula, ih, update_eq_base]

/--
`liftFormula` is also semantics-preserving when starting from an arbitrary Henkin model
and lowering it to a base FO model.
-/
theorem forces_liftFormula_iff_lowerModel
    {W : Type} [Preorder W] {σ κ D : Type}
    (MH : Model W σ D)
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
    (η : ParamInterp κ D)
    (w : W) (φ : Formula σ) :
    Forces MH ρ η w (liftFormula (σ := σ) (κ := κ) φ) ↔
      HeytingLean.Noneism.KripkeFO.Forces (lowerModel MH) ρ w φ := by
  simpa [liftModel_lowerModel] using
    (forces_liftFormula_iff
      (M := lowerModel MH)
      (ρ := ρ) (η := η)
      (w := w) (φ := φ))

/--
Pointwise context transfer for lifted formulas.
-/
theorem forces_liftContext_iff
    {W : Type} [Preorder W] {σ κ D : Type}
    (M : HeytingLean.Noneism.KripkeFO.Model W σ D)
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
    (η : ParamInterp κ D)
    (w : W) (Γ : List (Formula σ)) :
    (∀ ψ ∈ Γ, Forces (liftModel M) ρ η w (liftFormula (σ := σ) (κ := κ) ψ)) ↔
      (∀ ψ ∈ Γ, HeytingLean.Noneism.KripkeFO.Forces M ρ w ψ) := by
  constructor
  · intro h ψ hψ
    exact (forces_liftFormula_iff (M := M) (ρ := ρ) (η := η) w ψ).1 (h ψ hψ)
  · intro h ψ hψ
    exact (forces_liftFormula_iff (M := M) (ρ := ρ) (η := η) w ψ).2 (h ψ hψ)

end KripkeFOH
end Noneism
end HeytingLean
