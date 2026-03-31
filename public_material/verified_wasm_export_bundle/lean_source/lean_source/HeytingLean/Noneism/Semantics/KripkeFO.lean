import Mathlib.Order.Basic
import HeytingLean.Noneism.Syntax.Subst

/-!
# Noneism.Semantics.KripkeFO

Kripke semantics for the **first-order-ish** `Noneism.Syntax` language:
- Worlds form a preorder.
- Terms are just variables (`Term.var`), interpreted by a valuation `Var → D`.
- `pred` and `eExists` are interpreted as *atomic* predicates, but now they can depend on the
  interpreted term arguments / term value.
- Quantifiers (`sigma` / `pi`) are interpreted with a **constant domain** `D`.

This file is designed to support soundness of the ND system `Noneism.ProofTheory.ND.Derives`.
Completeness for the quantifier fragment is left for future work (it requires a more substantial
canonical model construction).

Design docs / blockers for the Henkin-style route live in:
- `WIP/noneism_fo_henkin_completeness_plan_2026-02-09.md`
- `WIP/noneism_fo_henkin_completeness_2026-02-11.md`
- `WIP/noneism_henkin_one_step_extension_2026-02-11.md`
- `WIP/noneism_internal_fo_completeness_blockers_2026-02-06.md`
- `Blueprint/noneism_henkin_trackA_execution_blueprint_2026-02-11.md`
-/

namespace HeytingLean
namespace Noneism

open Formula

namespace KripkeFO

/-! ## Valuations and term evaluation -/

/-- Variable assignment. -/
abbrev Valuation (D : Type) := Var → D

/-- Update a valuation at variable `x`. -/
def update {D} (ρ : Valuation D) (x : Var) (d : D) : Valuation D :=
  fun y => if y = x then d else ρ y

@[simp] theorem update_self {D} (ρ : Valuation D) (x : Var) (d : D) :
    update ρ x d x = d := by
  simp [update]

@[simp] theorem update_other {D} (ρ : Valuation D) (x y : Var) (d : D) (h : y ≠ x) :
    update ρ x d y = ρ y := by
  simp [update, h]

theorem update_update_same {D} (ρ : Valuation D) (x : Var) (d₁ d₂ : D) :
    update (update ρ x d₁) x d₂ = update ρ x d₂ := by
  funext y
  by_cases hy : y = x <;> simp [update, hy]

theorem update_comm {D} (ρ : Valuation D) {x y : Var} (dx dy : D) (h : x ≠ y) :
    update (update ρ x dx) y dy = update (update ρ y dy) x dx := by
  funext z
  by_cases hzx : z = x
  · subst hzx
    simp [update, h]
  · by_cases hzy : z = y
    · subst hzy
      simp [update, hzx]
    · simp [update, hzx, hzy]

/-- Evaluate a term under a valuation. -/
def evalTerm {D} (ρ : Valuation D) : Term → D
  | .var x => ρ x

/-! ## Frames and models -/

/-- A Kripke model over worlds `W` and constant domain `D`. -/
structure Model (W : Type) (σ : Type) (D : Type) [Preorder W] where
  /-- Atomic valuation for `pred`. Must be monotone in the world order. -/
  valPred : W → σ → List D → Prop
  monoPred : ∀ {w v : W}, w ≤ v → ∀ p args, valPred w p args → valPred v p args
  /-- Atomic valuation for `eExists`. Must be monotone in the world order. -/
  valEx : W → D → Prop
  monoEx : ∀ {w v : W}, w ≤ v → ∀ d, valEx w d → valEx v d

/-! ## Forcing -/

/-- Forcing relation (Kripke) with an explicit valuation for variables. -/
def Forces {W : Type} [Preorder W] {σ D : Type} (M : Model W σ D) (ρ : Valuation D) :
    W → Formula σ → Prop
  | _, .top => True
  | _, .bot => False
  | w, .pred p args => M.valPred w p (args.map (evalTerm ρ))
  | w, .eExists t => M.valEx w (evalTerm ρ t)
  | w, .not φ => ∀ v, w ≤ v → Forces M ρ v φ → False
  | w, .and φ ψ => Forces M ρ w φ ∧ Forces M ρ w ψ
  | w, .or φ ψ => Forces M ρ w φ ∨ Forces M ρ w ψ
  | w, .imp φ ψ => ∀ v, w ≤ v → Forces M ρ v φ → Forces M ρ v ψ
  | w, .sigma x φ => ∃ d : D, Forces M (update ρ x d) w φ
  | w, .pi x φ => ∀ v, w ≤ v → ∀ d : D, Forces M (update ρ x d) v φ

/-! ## Semantic entailment -/

/-- Semantic entailment (at all worlds of all models, for all valuations). -/
def Entails {σ : Type} (Γ : List (Formula σ)) (φ : Formula σ) : Prop :=
  ∀ (W : Type) [Preorder W] (D : Type) (M : Model W σ D) (ρ : Valuation D) (w : W),
    (∀ ψ ∈ Γ, Forces M ρ w ψ) → Forces M ρ w φ

end KripkeFO

end Noneism
end HeytingLean
