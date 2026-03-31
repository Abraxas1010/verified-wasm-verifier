import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Spectral Contract Layer (Continual Learning)

Contract-first theorem scaffolding for normalized Laplacian claims used by the
continual-learning spectral program.

This module is intentionally assumption-explicit: we encode the spectral facts
as contract fields and prove downstream consequences from those fields.
-/

namespace HeytingLean
namespace Analysis
namespace Graph

open Matrix

/-- Positive semidefinite quadratic-form contract for a matrix. -/
def IsPSD {n : Nat} (L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (L.mulVec x)

/-- Contract interface for normalized Laplacian properties used by CL claims. -/
structure NormalizedLaplacianContract (n : Nat) where
  /-- Candidate normalized Laplacian matrix. -/
  L : Matrix (Fin n) (Fin n) ℝ
  /-- Symmetry contract. -/
  symm : Matrix.IsSymm L
  /-- PSD contract. -/
  psd : IsPSD L
  /-- Reported second eigenvalue (`λ₂`) from runtime/solver layer. -/
  lambda2 : ℝ
  /-- Nonnegativity contract for `λ₂`. -/
  lambda2_nonneg : 0 ≤ lambda2
  /-- Connectivity predicate attached to the same graph/model. -/
  connected : Prop
  /-- Fiedler-style contract: connected iff `λ₂ > 0`. -/
  connected_iff_lambda2_pos : connected ↔ 0 < lambda2

namespace NormalizedLaplacianContract

variable {n : Nat} (C : NormalizedLaplacianContract n)

/-- Contract theorem: normalized Laplacian quadratic form is nonnegative. -/
theorem normalized_laplacian_psd : IsPSD C.L :=
  C.psd

/-- Contract theorem: `λ₂` is nonnegative. -/
theorem lambda2_nonnegative : 0 ≤ C.lambda2 :=
  C.lambda2_nonneg

/-- Contract theorem: connectivity equivalence with strict positivity of `λ₂`. -/
theorem connected_iff_lambda2_pos_contract : C.connected ↔ 0 < C.lambda2 :=
  C.connected_iff_lambda2_pos

/-- Convenience direction: connected implies strictly positive `λ₂`. -/
theorem lambda2_pos_of_connected (hconn : C.connected) : 0 < C.lambda2 :=
  (C.connected_iff_lambda2_pos_contract).1 hconn

/-- Convenience direction: positive `λ₂` implies connected. -/
theorem connected_of_lambda2_pos (hpos : 0 < C.lambda2) : C.connected :=
  (C.connected_iff_lambda2_pos_contract).2 hpos

/-- If `λ₂ = 0`, connectivity is impossible under the contract. -/
theorem not_connected_of_lambda2_eq_zero (hz : C.lambda2 = 0) : ¬ C.connected := by
  intro hconn
  have hpos : 0 < C.lambda2 := C.lambda2_pos_of_connected hconn
  have hnot : ¬ (0 < C.lambda2) := by simp [hz]
  exact hnot hpos

end NormalizedLaplacianContract

end Graph
end Analysis
end HeytingLean
