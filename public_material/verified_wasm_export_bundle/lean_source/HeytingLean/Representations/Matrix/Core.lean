import Mathlib.Data.Matrix.Basic

/-!
# Matrix representations (lens layer scaffold)

This folder provides a small, reusable interface for representing “lens values” as square matrices.

It is intentionally interface-first: most downstream code in HeytingLean uses higher-level “lens”
contracts (round-trip carriers). A `LensRepr` provides an additional concrete view that can be used
for linear-algebraic semantics and executable checks.
-/

namespace HeytingLean
namespace Representations
namespace Matrix

universe u v

/-- A representation of `L` by `n×n` matrices over `R`. -/
class LensRepr (L : Type u) (n : ℕ) (R : Type v) [Semiring R] [One L] [Mul L] where
  /-- The representation map. -/
  toMatrix : L → Matrix (Fin n) (Fin n) R
  /-- Representation preserves identity. -/
  toMatrix_one : toMatrix (1 : L) = 1
  /-- Representation preserves multiplication. -/
  toMatrix_mul : ∀ a b : L, toMatrix (a * b) = toMatrix a * toMatrix b

/-- A faithful representation is injective. -/
class FaithfulRepr (L : Type u) (n : ℕ) (R : Type v) [Semiring R] [One L] [Mul L]
    extends LensRepr L n R where
  injective : Function.Injective toMatrix

attribute [simp] LensRepr.toMatrix_one LensRepr.toMatrix_mul

end Matrix
end Representations
end HeytingLean
