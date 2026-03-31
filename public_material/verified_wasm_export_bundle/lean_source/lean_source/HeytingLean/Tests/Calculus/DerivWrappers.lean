import HeytingLean.Calculus.DerivMathlib

/-! Compile-only sanity checks for derivative wrappers. -/

namespace HeytingLean
namespace Tests
namespace Calculus

open HeytingLean.Calculus

example : deriv (fun _ : ℝ => (3 : ℝ)) = fun _ => 0 := by
  simpa using deriv_const' (c := (3 : ℝ))

-- identity derivative (sanity)
example : deriv (fun x : ℝ => x) = fun _ => (1 : ℝ) := by
  simpa using deriv_id'

/-- Use addition/product/chain derivative wrappers in a single definition to
ensure they typecheck and are available. -/
def _wrappersDemo : Unit := by
  have hf : Differentiable ℝ (fun x : ℝ => x) := by
    simpa using (differentiable_id (𝕜 := ℝ))
  have hg : Differentiable ℝ (fun _ : ℝ => (5 : ℝ)) := by
    simpa using (differentiable_const (c := (5 : ℝ)))
  let _ := deriv_add' (f := fun x : ℝ => x) (g := fun _ : ℝ => (5 : ℝ)) hf hg
  let _ := deriv_mul' (f := fun x : ℝ => x) (g := fun x : ℝ => x) hf hf
  let _ := deriv_chain' (f := fun x : ℝ => x) (g := fun x : ℝ => x) hf hf
  exact ()

-- affine rule
example : deriv (fun x : ℝ => (2 : ℝ) * x + (5 : ℝ)) = fun _ => (2 : ℝ) := by
  simpa using deriv_affine' (a := (2 : ℝ)) (b := (5 : ℝ))

-- Keep this file compile-only; no heavy goals.

-- We refrain from reducing pointwise equalities here to keep the test compile-only.

end Calculus
end Tests
end HeytingLean
