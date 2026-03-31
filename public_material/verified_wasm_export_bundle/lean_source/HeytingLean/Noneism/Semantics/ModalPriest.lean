import HeytingLean.Noneism.Syntax

namespace HeytingLean
namespace Noneism
namespace ModalPriest

/-- World kind: actual, possible, or impossible. -/
inductive Kind | α | P | I deriving DecidableEq, Repr

/-- Minimal Priest-style modal model. -/
structure Model (σ D : Type) where
  W        : Type
  kind     : W → Kind
  α        : W                     -- designated actual world
  interp   : W → σ → (List D → Prop)
  existsP  : W → D → Prop
  about    : W → D → Prop          -- aboutness at a world
  realize  : (D → Prop) → (W → Prop)    -- realization set as a predicate on worlds
  item     : (D → Prop) → D        -- item created by comprehension for that characterization

/-- For the trivial characterization `χ := True`, any assumed realization
at a world `w` is itself a witness; this is a bookkeeping lemma, not a
standalone “smoke” theorem. -/
theorem cp_holdsTrue {σ D} (M : Model σ D) {w : M.W}
    (hw : M.realize (fun _ : D => True) w) :
    M.realize (fun _ : D => True) w :=
  hw

/-- Variable assignment. -/
abbrev Valuation (D : Type) := Noneism.Var → D

/-- Update a valuation at variable `x`. -/
def update {D} (ρ : Valuation D) (x : Noneism.Var) (d : D) : Valuation D :=
  fun y => if y = x then d else ρ y

/-- Evaluate a term under a valuation. -/
def evalTerm {D} (ρ : Valuation D) : Noneism.Term → D
  | .var x => ρ x

/-- Modal Priest satisfaction: evaluate an object-language formula at world `w`. -/
def eval {σ D} (M : Model σ D) (ρ : Valuation D) (w : M.W)
    (φ : Noneism.Formula σ) : Prop :=
  match φ with
  | .top        => True
  | .bot        => False
  | .pred p ts  => M.interp w p (ts.map (evalTerm ρ))
  | .eExists t  => M.existsP w (evalTerm ρ t)
  | .not φ      => ¬ eval M ρ w φ
  | .and φ ψ    => eval M ρ w φ ∧ eval M ρ w ψ
  | .or  φ ψ    => eval M ρ w φ ∨ eval M ρ w ψ
  | .imp φ ψ    => eval M ρ w φ → eval M ρ w ψ
  | .sigma x φ  => ∃ d : D, eval M (update ρ x d) w φ
  | .pi    x φ  => ∀ d : D, eval M (update ρ x d) w φ

/-- Evaluating the top formula is definitionally `True`. -/
@[simp] theorem eval_top {σ D} (M : Model σ D) (ρ : Valuation D) (w : M.W) :
    eval M ρ w (.top : Noneism.Formula σ) = True := by
  -- By unfolding `eval`, the `.top` case reduces to `True`.
  rfl

/-- Evaluating the bottom formula is definitionally `False`. -/
@[simp] theorem eval_bot {σ D} (M : Model σ D) (ρ : Valuation D) (w : M.W) :
    eval M ρ w (.bot : Noneism.Formula σ) = False := by
  -- By unfolding `eval`, the `.bot` case reduces to `False`.
  rfl

/-- Evaluating a conjunction is definitionally the conjunction of evaluations. -/
@[simp] theorem eval_and {σ D} (M : Model σ D) (ρ : Valuation D) (w : M.W)
    (φ ψ : Noneism.Formula σ) :
    eval M ρ w (.and φ ψ) ↔
      eval M ρ w φ ∧ eval M ρ w ψ := by
  -- This follows directly from the definition of `eval`.
  rfl

/-- Evaluating a disjunction is definitionally the disjunction of evaluations. -/
@[simp] theorem eval_or {σ D} (M : Model σ D) (ρ : Valuation D) (w : M.W)
    (φ ψ : Noneism.Formula σ) :
    eval M ρ w (.or φ ψ) ↔
      eval M ρ w φ ∨ eval M ρ w ψ := by
  -- This follows directly from the definition of `eval`.
  rfl

/-- Evaluating an implication is definitionally the implication of evaluations. -/
@[simp] theorem eval_imp {σ D} (M : Model σ D) (ρ : Valuation D) (w : M.W)
    (φ ψ : Noneism.Formula σ) :
    eval M ρ w (.imp φ ψ) =
      (eval M ρ w φ → eval M ρ w ψ) := by
  -- This follows directly from the definition of `eval`.
  rfl

end ModalPriest
end Noneism
end HeytingLean
