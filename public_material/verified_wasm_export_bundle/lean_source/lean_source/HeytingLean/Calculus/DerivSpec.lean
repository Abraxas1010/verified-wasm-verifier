/-!
Derivative specifications (signature only, no heavy analysis imports).

This module describes the **shape** of the basic algebraic laws we expect
from an abstract derivative combinator `D : (α → α) → (α → α)` on a
semiring `α`.  We deliberately do *not* provide any default instance or
trivial proofs here: concrete analysis-heavy backends are free to
instantiate these axioms against `Real`, `ℝ≥0`, etc., in more specialised
modules.
-/

universe u

namespace HeytingLean
namespace Calculus

/-- A minimal axiomatization of a derivative combinator on an abstract
algebraic carrier.

The record lives in `Prop`: inhabiting it corresponds to *assuming* the
usual algebraic laws for a chosen operator `D`, without baking any fake or
trivial proofs into the core library.
-/
structure DerivAxioms (α : Type u)
    (zero : α) (add mul : α → α → α)
    (D : (α → α) → (α → α)) : Prop where
  /-- Derivative of a constant function is identically zero. -/
  derivConst_ok :
    ∀ c : α, D (fun _ => c) = fun _ => zero
  /-- Derivative distributes over pointwise addition. -/
  derivAdd_ok :
    ∀ f g : α → α,
      D (fun x => add (f x) (g x)) =
        fun x => add (D f x) (D g x)
  /-- Product rule for the derivative combinator. -/
  derivMul_ok :
    ∀ f g : α → α,
      D (fun x => mul (f x) (g x)) =
        fun x => add (mul (D f x) (g x)) (mul (f x) (D g x))
  /-- Derivative of an affine map `x ↦ a * x + b` is the constant `a`. -/
  derivAffine_ok :
    ∀ a b : α,
      D (fun x => add (mul a x) b) = fun _ => a

end Calculus
end HeytingLean
