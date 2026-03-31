import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
	Mathlib-backed derivative theorems (auxiliary import module).
	When the mathlib pin includes calculus, add wrappers here that export
	the core derivative rules (constants, affine, add, mul, chain).
	This file is intentionally not imported by the aggregator to keep
	everyday builds fast; build it explicitly when needed.
	-/

namespace HeytingLean
namespace Calculus

noncomputable section

open scoped Classical

variable {f g : ℝ → ℝ}

@[simp] theorem deriv_const' (c : ℝ) :
  deriv (fun _x : ℝ => c) = fun _ => 0 := by
  simpa using (deriv_const (c := c))

@[simp] theorem deriv_id' :
  deriv (fun x : ℝ => x) = fun _ => (1 : ℝ) := by
  simpa using (deriv_id (𝕜 := ℝ))

/-- Addition rule, lifted to a function equality. -/
@[simp] theorem deriv_add'
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    deriv (fun x => f x + g x) = fun x => deriv f x + deriv g x := by
  funext x; simpa using (deriv_add (hf x) (hg x))

/-- Product rule, lifted to a function equality. -/
@[simp] theorem deriv_mul'
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    deriv (fun x => f x * g x) = fun x => deriv f x * g x + f x * deriv g x := by
  funext x; simpa using (deriv_mul (hf x) (hg x))

/-- Chain rule, lifted to a function equality. -/
@[simp] theorem deriv_chain'
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    deriv (fun x => f (g x)) = fun x => deriv f (g x) * deriv g x := by
  funext x; simpa [Function.comp] using (deriv_comp (hh₂ := hf (g x)) (hh := hg x))

/-- Affine rule: `x ↦ a*x + b` has derivative `a` (functionally constant). -/
@[simp] theorem deriv_affine' (a b : ℝ) :
  deriv (fun x : ℝ => a * x + b) = fun _ => a := by
  -- use `deriv_add_const` then `deriv_const_mul` on `id`.
  funext x
  have : deriv (fun y : ℝ => a * y + b) x = deriv (fun y : ℝ => a * y) x := by
    simpa using (deriv_add_const (f := fun y : ℝ => a * y) (x := x) (c := b))
  have hx : DifferentiableAt ℝ (fun y : ℝ => y) x := by simpa using (differentiableAt_id (𝕜 := ℝ))
  have hmul : deriv (fun y : ℝ => a * y) x = a * deriv (fun y : ℝ => y) x := by
    simpa using (deriv_const_mul (c := a) (hd := hx))
  simpa [this, hmul, deriv_id']

end

/-- Real-level derivative laws backing the abstract calculus specification.

This record packages the standard one-dimensional derivative rules for
`ℝ → ℝ` functions that are differentiable in the sense of mathlib.  It
plays the role of a concrete backend for the abstract
`DerivAxioms` schema: the shape of the axioms matches the calculus
rules, but the hypotheses are made explicit rather than hidden behind
trivial proofs.
-/
structure RealDerivLaws : Prop where
  /-- Derivative of a constant function is zero everywhere. -/
  derivConst_ok :
    ∀ c : ℝ, deriv (fun _ : ℝ => c) = fun _ => (0 : ℝ)
  /-- Addition rule under differentiability assumptions. -/
  derivAdd_ok :
    ∀ f g : ℝ → ℝ,
      Differentiable ℝ f → Differentiable ℝ g →
        deriv (fun x => f x + g x) =
          fun x => deriv f x + deriv g x
  /-- Product rule under differentiability assumptions. -/
  derivMul_ok :
    ∀ f g : ℝ → ℝ,
      Differentiable ℝ f → Differentiable ℝ g →
        deriv (fun x => f x * g x) =
          fun x => deriv f x * g x + f x * deriv g x
  /-- Derivative of an affine map `x ↦ a * x + b` is the constant `a`. -/
  derivAffine_ok :
    ∀ a b : ℝ,
      deriv (fun x : ℝ => a * x + b) = fun _ => a

/-- The mathlib derivative on `ℝ → ℝ` functions satisfies the expected
constant, addition, product, and affine rules under the usual
differentiability hypotheses. -/
lemma realDerivLaws : RealDerivLaws := by
  refine ⟨?c, ?add, ?mul, ?aff⟩
  · intro c
    simpa using deriv_const' (c := c)
  · intro f g hf hg
    simpa using deriv_add' (f := f) (g := g) hf hg
  · intro f g hf hg
    simpa using deriv_mul' (f := f) (g := g) hf hg
  · intro a b
    simpa using deriv_affine' (a := a) (b := b)

end Calculus
end HeytingLean
