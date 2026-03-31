import HeytingLean.Analysis.Lyapunov.Certificate

/-!
# Stable Generator Construction

This module provides the stable generator construction `G = -(A^T A) + (B - B^T)`
which guarantees that G is Hurwitz when A has full rank.

## Main Results

* `stableGenerator`: The construction `G = -(A^T A) + (B - B^T)`
* `stableGenerator_symm_part`: The symmetric part of G is `-(A^T A)`
* `stableGenerator_hurwitz`: G is Hurwitz when A has full rank

## Mathematical Background

For any matrices A ∈ ℝ^{n×m} with full column rank and B ∈ ℝ^{n×n}:
- `A^T A` is positive definite (all eigenvalues > 0)
- `B - B^T` is skew-symmetric (all eigenvalues are purely imaginary)
- `G = -(A^T A) + (B - B^T)` has symmetric part `-(A^T A)` (negative definite)

For a symmetric matrix, negative definiteness of the symmetric part implies
all eigenvalues have negative real parts, hence G is Hurwitz.

## References

* The construction is standard in Koopman NBA (Neural Born Approximation) for
  ensuring stable learned dynamics.
-/

noncomputable section

open scoped Matrix BigOperators

namespace HeytingLean
namespace Analysis
namespace Lyapunov

variable {n m : ℕ}

/-! ## Stable Generator Construction -/

/-- The stable generator: `G = -(A A^T) + (B - B^T)` for A : n × m. -/
def stableGenerator (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n) : RMat n :=
  -(A * A.transpose) + (B - B.transpose)

/-- The symmetric part of the stable generator is `-(A A^T)`. -/
theorem stableGenerator_symm_part (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n) :
    symmetricPart (stableGenerator A B) = -(A * A.transpose) := by
  ext i j
  simp only [symmetricPart, stableGenerator, Matrix.smul_apply, Matrix.add_apply,
             Matrix.neg_apply, Matrix.sub_apply, Matrix.transpose_add,
             Matrix.transpose_neg, Matrix.transpose_sub, Matrix.transpose_transpose,
             Matrix.transpose_mul, smul_eq_mul]
  ring

/-- The skew-symmetric part of the stable generator is `(B - B^T)`. -/
theorem stableGenerator_skew_part (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n) :
    skewSymmetricPart (stableGenerator A B) = B - B.transpose := by
  ext i j
  simp only [skewSymmetricPart, stableGenerator, Matrix.smul_apply, Matrix.add_apply,
             Matrix.neg_apply, Matrix.sub_apply, Matrix.transpose_add,
             Matrix.transpose_neg, Matrix.transpose_sub, Matrix.transpose_transpose,
             Matrix.transpose_mul, smul_eq_mul]
  ring

/-- The decomposition of the stable generator. -/
theorem stableGenerator_decomp (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n) :
    stableGenerator A B = symmetricPart (stableGenerator A B) +
                           skewSymmetricPart (stableGenerator A B) := by
  rw [stableGenerator_symm_part, stableGenerator_skew_part]
  simp only [stableGenerator]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply]
  ring

/-! ## Properties of A A^T -/

/-- A A^T is symmetric. -/
theorem aat_symmetric (A : Matrix (Fin n) (Fin m) ℝ) :
    (A * A.transpose).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.transpose_apply, star_trivial]
  congr 1
  ext k
  ring

/-- A A^T is positive semidefinite: x^T (A A^T) x = ||A^T x||² ≥ 0. -/
theorem aat_posSemidef (A : Matrix (Fin n) (Fin m) ℝ) :
    ∀ x : Fin n → ℝ, 0 ≤ dot x ((A * A.transpose).mulVec x) := by
  intro x
  simp only [dot, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply]
  -- x^T A A^T x = ||A^T x||² = sum_j (sum_i A_ij x_i)^2
  have h : ∑ i, x i * ∑ j, A i j * (∑ k, A k j * x k) =
           ∑ j, (∑ i, A i j * x i)^2 := by
    simp only [sq]
    rw [Finset.sum_comm]
    congr 1
    ext j
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    congr 1
    ext i
    ring
  rw [h]
  apply Finset.sum_nonneg
  intro j _
  exact sq_nonneg _

/-! ## Hurwitz Property -/

/-- If A A^T is positive definite (A has full row rank), then the stable generator is Hurwitz.
    This is the key theorem for Koopman NBA stability.

    NOTE: Full proof requires spectral theory. The key insight is that for any
    eigenvalue λ of G with eigenvector v:
    - λ = v^* G v / (v^* v) (Rayleigh quotient)
    - Re(λ) = v^* (sym G) v / (v^* v) (real part from symmetric part)
    - sym G = -(A A^T) negative definite implies Re(λ) < 0 -/
theorem stableGenerator_hurwitz (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n)
    (hA : (A * A.transpose).PosDef) :
    IsHurwitz (stableGenerator A B) := by
  -- IsHurwitz is defined as existence of Lyapunov function
  -- Use P = I and Q = 2(A A^T)
  use 1, 2 • (A * A.transpose)
  refine ⟨?_, ?_, ?_⟩
  · -- P = I is positive definite
    exact Matrix.PosDef.one
  · -- Q = 2(A A^T) is positive definite when A A^T is
    exact Matrix.PosDef.smul (by norm_num : (0 : ℝ) < 2) hA
  · -- Lyapunov equation: G^T I + I G = -2(A A^T)
    unfold SatisfiesLyapunov stableGenerator
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
               Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_add,
               Matrix.transpose_neg, Matrix.transpose_sub, Matrix.transpose_transpose,
               Matrix.transpose_mul, Matrix.mul_one, Matrix.one_mul,
               Matrix.sub_apply, smul_eq_mul]
    ring

/-! ## Lyapunov Equation for Stable Generator -/

/-- The stable generator satisfies a Lyapunov equation with P = I and Q = 2(A A^T).
    That is: G^T I + I G = -2(A A^T).

    Proof: G^T + G = [-(A A^T) + (B - B^T)]^T + [-(A A^T) + (B - B^T)]
                   = -(A A^T) + (B^T - B) + -(A A^T) + (B - B^T)
                   = -2(A A^T) -/
theorem stableGenerator_lyapunov (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n) :
    SatisfiesLyapunov (stableGenerator A B) 1 (2 • (A * A.transpose)) := by
  unfold SatisfiesLyapunov stableGenerator
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
             Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_add,
             Matrix.transpose_neg, Matrix.transpose_sub, Matrix.transpose_transpose,
             Matrix.transpose_mul, Matrix.mul_one, Matrix.one_mul,
             Matrix.sub_apply, smul_eq_mul]
  ring

/-! ## Certificate Construction -/

/-- Construct a Lyapunov certificate for a stable generator. -/
def stableGeneratorCertificate (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n)
    (minEigAAT maxEigSymG : ℝ) : LyapunovCertificate n where
  G := stableGenerator A B
  P := 1
  Q := 2 • (A * A.transpose)
  minEigP := 1  -- Identity has eigenvalue 1
  maxEigSymG := maxEigSymG
  residualBound := 0  -- Exact Lyapunov equation

/-- The stable generator certificate satisfies the Lyapunov equation. -/
theorem stableGeneratorCertificate_lyapunov (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n)
    (minEigAAT maxEigSymG : ℝ) :
    (stableGeneratorCertificate A B minEigAAT maxEigSymG).claimsLyapunov := by
  simp only [LyapunovCertificate.claimsLyapunov, stableGeneratorCertificate]
  exact stableGenerator_lyapunov A B

/-- The stable generator certificate has P = I positive definite (minEigP = 1 > 0). -/
theorem stableGeneratorCertificate_minEigP (A : Matrix (Fin n) (Fin m) ℝ) (B : RMat n)
    (minEigAAT maxEigSymG : ℝ) :
    (stableGeneratorCertificate A B minEigAAT maxEigSymG).minEigP = 1 := rfl

end Lyapunov
end Analysis
end HeytingLean

end
