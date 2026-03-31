import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lyapunov Stability: Basic Definitions

This module provides core definitions for Lyapunov stability analysis of linear
time-invariant (LTI) systems `ẋ = Gx`. The main components are:

1. **Continuous Lyapunov equation**: `G^T P + P G = -Q`
2. **Stability conditions** based on positive definiteness
3. **Hurwitz matrices** (all eigenvalues have negative real part)

## Main Definitions

* `RMat n`: Real n×n matrices
* `SatisfiesLyapunov`: The Lyapunov equation predicate
* `IsHurwitz`: Matrix has all eigenvalues with negative real part (oracle-based)
* `symmetricPart`: The symmetric part `(G + G^T)/2` of a matrix

## References

* Khalil, H. K. "Nonlinear Systems" (3rd ed.), Prentice Hall, 2002
* Lyapunov, A. M. "The General Problem of the Stability of Motion", 1892
-/

noncomputable section

open scoped Matrix BigOperators

namespace HeytingLean
namespace Analysis
namespace Lyapunov

/-- Real n×n matrices. -/
abbrev RMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

/-! ## Dot Product for Real Vectors -/

/-- Dot product of real vectors. -/
def dot (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

theorem dot_comm (x y : Fin n → ℝ) : dot x y = dot y x := by
  simp only [dot, mul_comm]

/-! ## Lyapunov Equation -/

/-- The continuous Lyapunov equation: `G^T P + P G = -Q`. -/
def SatisfiesLyapunov (G P Q : RMat n) : Prop :=
  G.transpose * P + P * G = -Q

/-- Alternative formulation for symmetric P and Q. -/
theorem satisfiesLyapunov_iff_symm (G P Q : RMat n) :
    SatisfiesLyapunov G P Q ↔ G.transpose * P + P * G = -Q := Iff.rfl

/-! ## Symmetric Part -/

/-- The symmetric part of a matrix: `(G + G^T)/2`. -/
def symmetricPart (G : RMat n) : RMat n :=
  (1/2 : ℝ) • (G + G.transpose)

theorem symmetricPart_isHermitian (G : RMat n) : (symmetricPart G).IsHermitian := by
  unfold symmetricPart Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
             Matrix.transpose_apply, star_trivial, smul_eq_mul]
  ring

/-- The skew-symmetric part of a matrix: `(G - G^T)/2`. -/
def skewSymmetricPart (G : RMat n) : RMat n :=
  (1/2 : ℝ) • (G - G.transpose)

theorem skewSymmetricPart_skew (G : RMat n) :
    (skewSymmetricPart G).transpose = -skewSymmetricPart G := by
  unfold skewSymmetricPart
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply,
             Matrix.neg_apply, smul_eq_mul]
  ring

/-- A matrix decomposes into symmetric and skew-symmetric parts. -/
theorem symmetricPart_add_skewSymmetricPart (G : RMat n) :
    symmetricPart G + skewSymmetricPart G = G := by
  unfold symmetricPart skewSymmetricPart
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.add_apply,
             Matrix.sub_apply, Matrix.transpose_apply, smul_eq_mul]
  ring

/-! ## Stability Predicates -/

/-- A matrix is Hurwitz if all eigenvalues have strictly negative real part.
    This is an oracle-based definition - numerical solvers certify this property.
    We define it abstractly as the existence of a Lyapunov function. -/
def IsHurwitz (G : RMat n) : Prop :=
  ∃ P Q : RMat n, P.PosDef ∧ Q.PosDef ∧ SatisfiesLyapunov G P Q

/-- A symmetric matrix is stable iff it is negative definite. -/
def IsStableSymm (G : RMat n) : Prop :=
  G.IsHermitian ∧ (∀ x : Fin n → ℝ, x ≠ 0 → dot x (G.mulVec x) < 0)

/-! ## Energy/Lyapunov Function -/

/-- The quadratic Lyapunov function `V(x) = x^T P x`. -/
def lyapunovFunction (P : RMat n) (x : Fin n → ℝ) : ℝ :=
  dot x (P.mulVec x)

/-- The time derivative of V along trajectories of `ẋ = Gx` is `x^T (G^T P + P G) x`. -/
def lyapunovDerivative (G P : RMat n) (x : Fin n → ℝ) : ℝ :=
  dot x ((G.transpose * P + P * G).mulVec x)

/-- When the Lyapunov equation holds, the derivative is `-x^T Q x`. -/
theorem lyapunovDerivative_eq_neg (G P Q : RMat n) (x : Fin n → ℝ)
    (hLyap : SatisfiesLyapunov G P Q) :
    lyapunovDerivative G P x = -dot x (Q.mulVec x) := by
  unfold lyapunovDerivative SatisfiesLyapunov at *
  rw [hLyap]
  simp only [Matrix.neg_mulVec, dot]
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

end Lyapunov
end Analysis
end HeytingLean

end
