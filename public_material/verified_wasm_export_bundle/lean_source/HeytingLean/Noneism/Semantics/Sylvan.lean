import HeytingLean.Noneism.Syntax

namespace HeytingLean
namespace Noneism
namespace Sylvan

open Noneism Formula

/-- A model over domain `D` interpreting predicate symbols `σ`. -/
structure Model (σ : Type) (D : Type) where
  interp  : σ → (List D → Prop)
  existsP : D → Prop

/-- Variable assignment. -/
abbrev Valuation (D : Type) := Noneism.Var → D

/-- Update a valuation at variable `x`. -/
def update {D} (ρ : Valuation D) (x : Noneism.Var) (d : D) : Valuation D :=
  fun y => if y = x then d else ρ y

theorem update_self {D} (ρ : Valuation D) (x : Noneism.Var) (d : D) :
    update ρ x d x = d := by
  simp [update]

theorem update_other {D} (ρ : Valuation D) (x y : Noneism.Var) (d : D)
    (h : y ≠ x) : update ρ x d y = ρ y := by
  simp [update, h]

/-- Evaluate a term under a valuation. -/
def evalTerm {D} (ρ : Valuation D) : Noneism.Term → D
  | .var x => ρ x

/-- Evaluate a formula under a model and valuation. -/
def eval {σ D} (M : Model σ D) (ρ : Valuation D)
    (φ : Noneism.Formula σ) : Prop :=
  match φ with
  | .top        => True
  | .bot        => False
  | .pred p ts  => M.interp p (ts.map (evalTerm ρ))
  | .eExists t  => M.existsP (evalTerm ρ t)
  | .not φ      => ¬ eval M ρ φ
  | .and φ ψ    => eval M ρ φ ∧ eval M ρ ψ
  | .or  φ ψ    => eval M ρ φ ∨ eval M ρ ψ
  | .imp φ ψ    => eval M ρ φ → eval M ρ ψ
  | .sigma x φ  => ∃ d : D, eval M (update ρ x d) φ
  | .pi    x φ  => ∀ d : D, eval M (update ρ x d) φ

-- UI/EG proofs will be added alongside richer semantics.

/-- Universal Instantiation (UI): from `Π x, φ` we get `φ` at any `d`. -/
theorem ui_pi {σ D} (M : Model σ D) (ρ : Valuation D)
    (x : Noneism.Var) (φ : Noneism.Formula σ) :
    eval M ρ (.pi x φ) → ∀ d : D, eval M (update ρ x d) φ := by
  intro h; simpa [eval] using h

/-- Existential Generalization (EG): from `Σ x, φ` obtain a witness. -/
theorem eg_sigma {σ D} (M : Model σ D) (ρ : Valuation D)
    (x : Noneism.Var) (φ : Noneism.Formula σ) :
    eval M ρ (.sigma x φ) → ∃ d : D, eval M (update ρ x d) φ := by
  intro h; simpa [eval] using h

end Sylvan
end Noneism
end HeytingLean
