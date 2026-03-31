import HeytingLean.Noneism.Syntax

namespace HeytingLean
namespace Noneism
namespace RM

/-- Minimal Routley–Meyer frame. -/
structure Frame (W : Type) where
  star : W → W
  R    : W → W → W → Prop

/-- A model with world-indexed predicate interpretation and optional existence. -/
structure Model (σ W D : Type) where
  F       : Frame W
  interp  : W → σ → (List D → Prop)
  existsP : W → D → Prop

/-- Variable assignment. -/
abbrev Valuation (D : Type) := Noneism.Var → D

/-- Update a valuation at variable `x`. -/
def update {D} (ρ : Valuation D) (x : Noneism.Var) (d : D) : Valuation D :=
  fun y => if y = x then d else ρ y

/-- Evaluate a term under a valuation. -/
def evalTerm {D} (ρ : Valuation D) : Noneism.Term → D
  | .var x => ρ x

/-- RM satisfaction: `sat M ρ w φ` means `φ` holds at world `w`. -/
def sat {σ W D} (M : Model σ W D) (ρ : Valuation D) (w : W)
    (φ : Noneism.Formula σ) : Prop :=
  match φ with
  | .top        => True
  | .bot        => False
  | .pred p ts  => M.interp w p (ts.map (evalTerm ρ))
  | .eExists t  => M.existsP w (evalTerm ρ t)
  | .not φ      => ¬ sat M ρ (M.F.star w) φ
  | .and φ ψ    => sat M ρ w φ ∧ sat M ρ w ψ
  | .or  φ ψ    => sat M ρ w φ ∨ sat M ρ w ψ
  | .imp φ ψ    => ∀ u v, M.F.R w u v → (sat M ρ u φ → sat M ρ v ψ)
  | .sigma x φ  => ∃ d : D, sat M (update ρ x d) w φ
  | .pi    x φ  => ∀ d : D, sat M (update ρ x d) w φ

/-- `Holds M ρ w φ` is just `sat M ρ w φ`. -/
def Holds {σ W D} (M : Model σ W D) (ρ : Valuation D) (w : W)
    (φ : Noneism.Formula σ) : Prop :=
  sat M ρ w φ

/-- RM semantic entailment at a fixed world (all models/valuations/worlds). -/
def Entails {σ : Type} (Γ : List (Noneism.Formula σ)) (φ : Noneism.Formula σ) : Prop :=
  ∀ (W D : Type) (M : Model σ W D) (ρ : Valuation D) (w : W),
    (∀ ψ ∈ Γ, sat M ρ w ψ) → sat M ρ w φ

-- Examples and countermodels live in the test module.

end RM
end Noneism
end HeytingLean
