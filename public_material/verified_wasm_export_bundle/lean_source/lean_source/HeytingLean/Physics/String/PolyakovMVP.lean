import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# PolyakovMVP (Path/Track B)

This module provides a *coordinate/linear-map* MVP of the Polyakov/sigma-model action.

We deliberately avoid manifold integration and analytic CFT. Instead we:
- model the field as a real matrix `A : Matrix (Fin d) (Fin 2) ℝ` (a linear map ℝ² → ℝᵈ),
- define the quadratic energy `frobSq A := trace (Aᵀ * A)` (sum of squares of entries),
- include a conformal (Weyl) scaling factor `conformalWeight Ω`,
  and prove it cancels in 2D for `Ω ≠ 0`,
- prove invariance of `frobSq` under orthogonal changes on the target/worldsheet side.

This lands the algebraic core that later geometric work must reproduce.
-/

noncomputable section

namespace HeytingLean
namespace Physics
namespace String
namespace PolyakovMVP

open scoped BigOperators
open scoped Matrix

variable {m n : Type} [Fintype m] [Fintype n]

/-- Squared Frobenius form for rectangular real matrices: `trace (Aᵀ A)`. -/
def frobSq (A : Matrix m n ℝ) : ℝ :=
  Matrix.trace (Aᵀ * A)

/-- Conformal/Weyl scaling factor for a 2D worldsheet metric `h = Ω² I`:
`√det(h) * h^{-1}` contributes a multiplicative factor `Ω² * Ω^{-2}`. -/
def conformalWeight (Ω : ℝ) : ℝ :=
  (Ω ^ 2) * (Ω⁻¹ ^ 2)

theorem conformalWeight_eq_one {Ω : ℝ} (hΩ : Ω ≠ 0) : conformalWeight Ω = 1 := by
  -- Pure algebra: (Ω²)(Ω⁻¹)² = (Ω*Ω)*(Ω⁻¹*Ω⁻¹) = (Ω*Ω⁻¹)*(Ω*Ω⁻¹) = 1.
  calc
    conformalWeight Ω = (Ω * Ω) * (Ω⁻¹ * Ω⁻¹) := by
      simp [conformalWeight, pow_two, mul_assoc]
    _ = (Ω * Ω⁻¹) * (Ω * Ω⁻¹) := by
      ac_rfl
    _ = 1 := by
      simp [mul_inv_cancel₀ hΩ]

/-- Polyakov action MVP: area × (conformal weight) × `frobSq`.

This models the *integrated* quadratic energy of a linear map on a flat patch of area `area`. -/
def polyakovAction (area Ω : ℝ) (A : Matrix m n ℝ) : ℝ :=
  area * conformalWeight Ω * frobSq A

theorem polyakovAction_conformal_invariant {area Ω : ℝ} (hΩ : Ω ≠ 0) (A : Matrix m n ℝ) :
    polyakovAction (m := m) (n := n) area Ω A = area * frobSq A := by
  simp [polyakovAction, conformalWeight_eq_one (hΩ := hΩ)]

theorem frobSq_mul_left_invariant {k : Type} [Fintype k] [DecidableEq k]
    (U : Matrix k k ℝ) (A : Matrix k n ℝ) (hU : Uᵀ * U = 1) :
    frobSq (m := k) (n := n) (U * A) = frobSq (m := k) (n := n) A := by
  classical
  -- (U A)ᵀ (U A) = Aᵀ Uᵀ U A = Aᵀ A when Uᵀ U = 1.
  unfold frobSq
  calc
    Matrix.trace ((U * A)ᵀ * (U * A))
        = Matrix.trace (Aᵀ * ((Uᵀ * U) * A)) := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (Aᵀ * A) := by
          simp [hU]

theorem frobSq_mul_right_invariant {k : Type} [Fintype k] [DecidableEq n]
    (A : Matrix k n ℝ) (V : Matrix n n ℝ) (hV : V * Vᵀ = 1) :
    frobSq (m := k) (n := n) (A * V) = frobSq (m := k) (n := n) A := by
  classical
  -- (A V)ᵀ (A V) = Vᵀ (Aᵀ A) V, and trace is cyclic: tr(Vᵀ N V) = tr(V Vᵀ N) = tr(N).
  unfold frobSq
  have h_expand : Matrix.trace ((A * V)ᵀ * (A * V)) = Matrix.trace (Vᵀ * (Aᵀ * A) * V) := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have h_cycle :
      Matrix.trace (Vᵀ * (Aᵀ * A) * V) = Matrix.trace ((V * Vᵀ) * (Aᵀ * A)) := by
    simpa [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle (A := Vᵀ) (B := (Aᵀ * A)) (C := V))
  rw [h_expand, h_cycle, hV]
  simp

end PolyakovMVP
end String
end Physics
end HeytingLean
