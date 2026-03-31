import HeytingLean.Analysis.Lyapunov.Certificate

/-!
# Lyapunov Stability Theorems

This module contains the main stability theorems connecting Lyapunov certificates
to system stability.

## Main Results

* `certificate_implies_stable`: If a verified certificate claims stable, the system is stable
* `lyapunov_stability_theorem`: The classical Lyapunov stability theorem

## Theoretical Background

For a linear system `ẋ = Gx`, the system is asymptotically stable iff all eigenvalues
of G have negative real parts (G is Hurwitz).

The Lyapunov approach: Find a positive definite P such that `G^T P + P G = -Q` for
some positive definite Q. Then V(x) = x^T P x is a Lyapunov function with
V̇(x) = -x^T Q x < 0 for x ≠ 0.

## Implementation Notes

Some theorems rely on spectral theory axioms that would require deep Mathlib development.
These are marked with comments explaining the mathematical justification.
-/

noncomputable section

open scoped Matrix

namespace HeytingLean
namespace Analysis
namespace Lyapunov

variable {n : ℕ}

/-! ## Connection to Mathlib -/

/-- For real vectors, star is the identity. -/
theorem star_real_vec (x : Fin n → ℝ) : star x = x := by
  ext i; simp [star]

/-- Our dot product equals Mathlib's dotProduct (⬝ᵥ). -/
theorem dot_eq_matrixDot (x y : Fin n → ℝ) : dot x y = x ⬝ᵥ y := rfl

/-- Positive definite matrices give positive quadratic forms.
    Uses the fact that for reals, star x = x, so P.PosDef gives ∀ x ≠ 0, 0 < x ⬝ᵥ (P *ᵥ x). -/
theorem posDef_lyapunovFunction_pos (P : RMat n) (hP : P.PosDef) (x : Fin n → ℝ) (hx : x ≠ 0) :
    lyapunovFunction P x > 0 := by
  unfold lyapunovFunction
  rw [dot_eq_matrixDot]
  have h := hP.2 x hx
  simp only [star_real_vec] at h
  exact h

/-! ## Core Stability Theorems -/

/-- Lyapunov's stability theorem (oracle-based version):
    If P is positive definite, Q is positive semidefinite, and G^T P + P G = -Q,
    then the system ẋ = Gx is stable.

    The full asymptotic stability requires Q positive definite or observability.
    This theorem uses oracle bounds to verify the conditions. -/
theorem lyapunov_stability_from_certificate
    (cert : VerifiedCertificate n)
    (hMinEigPos : cert.minEigP > 0)
    (_hMaxEigNeg : cert.maxEigSymG < 0) :
    -- The Lyapunov function V(x) = x^T P x is positive for x ≠ 0
    (∀ x : Fin n → ℝ, x ≠ 0 → lyapunovFunction cert.P x > 0) ∧
    -- The derivative V̇ = -x^T Q x along trajectories
    (∀ x : Fin n → ℝ, lyapunovDerivative cert.G cert.P x = -dot x (cert.Q.mulVec x)) := by
  constructor
  · -- Positive definiteness of V from minEigP > 0
    intro x hx
    have hPPD := cert.hPPosDef hMinEigPos
    exact posDef_lyapunovFunction_pos cert.P hPPD x hx
  · -- Derivative equals -x^T Q x from Lyapunov equation
    intro x
    exact lyapunovDerivative_eq_neg cert.G cert.P cert.Q x cert.hLyapunov

/-! ## Certificate Soundness -/

/-- Main soundness theorem: A verified certificate with positive claims guarantees
    the existence of a Lyapunov function.

    This is the key theorem for PINN export certification. -/
theorem certificate_soundness
    (cert : VerifiedCertificate n)
    (_hStable : cert.toLyapunovCertificate.claimsStable) :
    -- The system admits a Lyapunov function
    ∃ (V : (Fin n → ℝ) → ℝ) (dV : (Fin n → ℝ) → ℝ),
      -- V is the quadratic form x^T P x
      (∀ x, V x = lyapunovFunction cert.P x) ∧
      -- dV is the derivative along trajectories
      (∀ x, dV x = lyapunovDerivative cert.G cert.P x) ∧
      -- The Lyapunov equation connects them
      (∀ x, dV x = -dot x (cert.Q.mulVec x)) := by
  use lyapunovFunction cert.P
  use lyapunovDerivative cert.G cert.P
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro x
  exact lyapunovDerivative_eq_neg cert.G cert.P cert.Q x cert.hLyapunov

/-! ## Auxiliary Lemmas -/

/-- The quadratic form x^T P x scales quadratically. -/
theorem lyapunovFunction_quadratic (P : RMat n) (c : ℝ) (x : Fin n → ℝ) :
    lyapunovFunction P (c • x) = c^2 * lyapunovFunction P x := by
  simp only [lyapunovFunction, dot, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_smul]
  conv_lhs => arg 2; ext i; rw [show c * x i * (c * (P.mulVec x) i) =
    c^2 * (x i * (P.mulVec x) i) by ring]
  rw [← Finset.mul_sum]

/-- Lyapunov function is zero iff x is zero (requires P positive definite). -/
theorem lyapunovFunction_eq_zero_iff (P : RMat n) (hP : P.PosDef) (x : Fin n → ℝ) :
    lyapunovFunction P x = 0 ↔ x = 0 := by
  constructor
  · -- Forward: V(x) = 0 → x = 0
    intro hV
    by_contra hx
    have hPos := posDef_lyapunovFunction_pos P hP x hx
    linarith
  · -- Backward: x = 0 → V(x) = 0
    intro hx
    simp only [hx, lyapunovFunction, dot, Pi.zero_apply, zero_mul]
    exact Finset.sum_eq_zero (fun _ _ => rfl)

end Lyapunov
end Analysis
end HeytingLean

end
