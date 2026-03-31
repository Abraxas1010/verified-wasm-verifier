import Mathlib.Order.Basic
import HeytingLean.Noneism.Syntax

/-!
# Noneism.Semantics.KripkeProp

Kripke semantics for the **propositional fragment** of `HeytingLean.Noneism.Syntax`.

Key design choice:
- The current ND proof theory (`Noneism.ProofTheory.ND`) treats `pred p args` and `eExists t` as
  **atoms** (no special rules). Therefore this semantics also treats them as atoms, i.e. it does
  *not* interpret terms into a domain.

This file is intended to support a clean completeness theorem for the propositional ND system.
-/

namespace HeytingLean
namespace Noneism

open Formula

namespace KripkeProp

/-! ## Propositional-only predicate -/

/-- `IsProp φ` means `φ` contains no `sigma`/`pi` quantifiers. -/
inductive IsProp {σ : Type} : Formula σ → Prop
  | top : IsProp (.top : Formula σ)
  | bot : IsProp (.bot : Formula σ)
  | pred (p : σ) (args : List Term) : IsProp (.pred p args)
  | eExists (t : Term) : IsProp (.eExists t)
  | not {φ : Formula σ} : IsProp φ → IsProp (.not φ)
  | and {φ ψ : Formula σ} : IsProp φ → IsProp ψ → IsProp (.and φ ψ)
  | or  {φ ψ : Formula σ} : IsProp φ → IsProp ψ → IsProp (.or  φ ψ)
  | imp {φ ψ : Formula σ} : IsProp φ → IsProp ψ → IsProp (.imp φ ψ)

attribute [simp] IsProp.top IsProp.bot IsProp.pred IsProp.eExists

/-! ## Frames and models -/

/-- A Kripke model over a preorder of worlds `W`. -/
structure Model (W : Type) (σ : Type) [Preorder W] where
  /-- Atomic valuation for `pred`. Must be monotone in the world order. -/
  valPred : W → σ → List Term → Prop
  monoPred : ∀ {w v : W}, w ≤ v → ∀ p args, valPred w p args → valPred v p args
  /-- Atomic valuation for `eExists`. Must be monotone in the world order. -/
  valEx : W → Term → Prop
  monoEx : ∀ {w v : W}, w ≤ v → ∀ t, valEx w t → valEx v t

/-- Forcing relation in a model at a world (propositional fragment). -/
def Forces {W : Type} [Preorder W] {σ : Type} (M : Model W σ) : W → Formula σ → Prop
  | _, .top => True
  | _, .bot => False
  | w, .pred p args => M.valPred w p args
  | w, .eExists t => M.valEx w t
  /- Intuitionistic negation: definitional abbreviation for `φ → ⊥`. -/
  | w, .not φ => ∀ v, w ≤ v → Forces M v φ → False
  | w, .and φ ψ => Forces M w φ ∧ Forces M w ψ
  | w, .or  φ ψ => Forces M w φ ∨ Forces M w ψ
  | w, .imp φ ψ => ∀ v, w ≤ v → Forces M v φ → Forces M v ψ
  | _, .sigma _ _ => False
  | _, .pi _ _ => False

/-!
We deliberately interpret `sigma/pi` as `False` here because this file is for the propositional
fragment only. All soundness/completeness theorems below assume `IsProp` on the relevant formulas,
so the quantifier cases are unreachable.
-/

/-- Semantic entailment (at all worlds of all models). -/
def Entails {σ : Type} (Γ : List (Formula σ)) (φ : Formula σ) : Prop :=
  ∀ (W : Type) [Preorder W] (M : Model W σ) (w : W),
    (∀ ψ ∈ Γ, Forces M w ψ) → Forces M w φ

end KripkeProp

end Noneism
end HeytingLean
