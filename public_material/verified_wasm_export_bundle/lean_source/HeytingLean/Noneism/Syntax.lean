namespace HeytingLean
namespace Noneism

/-- Variables are de Bruijn-style indices. -/
abbrev Var := Nat

/-- Minimal term language: variables only (no function symbols). -/
inductive Term where
  | var (x : Var)
deriving DecidableEq, Repr

/-- Object-language formulas over a parameter type `σ` of predicate symbols. -/
inductive Formula (σ : Type) where
  | top
  | bot
  | pred (p : σ) (args : List Term)
  | eExists (t : Term)        -- existence predicate E!(t)
  | not (φ : Formula σ)
  | and (φ ψ : Formula σ)
  | or  (φ ψ : Formula σ)
  | imp (φ ψ : Formula σ)
  | sigma (x : Var) (φ : Formula σ)  -- neutral ∑
  | pi    (x : Var) (φ : Formula σ)  -- neutral ∏
deriving DecidableEq, Repr

namespace Formula
notation:max "¬ₙ" φ => Formula.not φ
notation:55 φ:55 " ∧ₙ " ψ:55 => Formula.and φ ψ
notation:50 φ:50 " ∨ₙ " ψ:50 => Formula.or φ ψ
notation:45 φ:45 " →ₙ " ψ:45 => Formula.imp φ ψ
end Formula

end Noneism
end HeytingLean

