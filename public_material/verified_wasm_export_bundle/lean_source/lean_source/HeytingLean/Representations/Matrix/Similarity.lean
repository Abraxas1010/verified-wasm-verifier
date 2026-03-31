import HeytingLean.Representations.Matrix.Eigenform
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Similarity transforms for matrices

We define a “change of basis” operation and record a few core invariants:

* Similar matrices have the same characteristic polynomial.
* Similarity is involutive under inverse change-of-basis.

This file is intentionally lightweight and executable-first.
-/

namespace HeytingLean
namespace Representations
namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {R : Type u} [CommRing R]

/-- Change of basis / similarity transform: `P⁻¹ * M * P`. -/
def changeBasis (M P : Matrix n n R) [Invertible P] : Matrix n n R :=
  (⅟ P) * M * P

theorem changeBasis_eq_units_conj (M P : Matrix n n R) [Invertible P] :
    changeBasis (M := M) (P := P) = (unitOfInvertible P)⁻¹.val * M * (unitOfInvertible P).val := by
  rfl

/-- Similarity preserves characteristic polynomial. -/
theorem similarity_preserves_charpoly (M P : Matrix n n R) [Invertible P] :
    (changeBasis (M := M) (P := P)).charpoly = M.charpoly := by
  -- `charpoly_units_conj'` states `(P⁻¹ * M * P).charpoly = M.charpoly`.
  simpa [changeBasis] using
    (Matrix.charpoly_units_conj' (M := unitOfInvertible P) (N := M))

/-- Changing basis twice by `P` and then by `P⁻¹` returns the original matrix. -/
theorem roundtrip_identity (M P : Matrix n n R) [Invertible P] :
    changeBasis (M := changeBasis (M := M) (P := P)) (P := (⅟ P)) = M := by
  -- Expand `changeBasis` and simplify using `invOf_mul_self`/`mul_invOf_self`.
  simp [changeBasis, mul_assoc]

end Matrix
end Representations
end HeytingLean
