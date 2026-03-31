import HeytingLean.Representations.Matrix.Core

/-!
# Tensor lens: matrices as-is

The simplest “lens to matrix” view: a tensor lens element is itself a matrix.
-/

namespace HeytingLean
namespace Representations
namespace Matrix
namespace Tensor

variable {n : ℕ} {R : Type} [Semiring R]

/-- Tensor lens elements represented directly as matrices. -/
abbrev TensorElem (n : ℕ) (R : Type) :=
  Matrix (Fin n) (Fin n) R

instance : LensRepr (TensorElem n R) n R where
  toMatrix := id
  toMatrix_one := by
    simp [TensorElem]
  toMatrix_mul := by
    intro a b
    rfl

end Tensor
end Matrix
end Representations
end HeytingLean
