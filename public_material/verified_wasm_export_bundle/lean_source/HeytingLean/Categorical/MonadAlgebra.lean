import HeytingLean.Core.Nucleus
import HeytingLean.Eigen.NucleusReLU
import Mathlib.Order.WithBot

/-!
# Monad Algebra Interface for Nucleus Operators

This file establishes that HeytingLean's nucleus operators form monad algebras
in the sense of Categorical Deep Learning (CDL).

## The Correspondence

A nucleus operator R : L → L on a meet-semilattice is exactly a monad algebra:

| Nucleus Property | Monad Algebra Axiom |
|------------------|---------------------|
| `extensive` (x ≤ R x) | η : Id → T (unit) |
| `idempotent` (R(R x) = R x) | μ : T² → T (multiplication coherence) |
| `meet_preserving` (R(x ⊓ y) = R x ⊓ R y) | strength σ : A × T B → T(A × B) |

## Reference

Gavranovic et al., "Categorical Deep Learning is an Algebraic Theory of All
Architectures", ICML 2024, arXiv:2402.15332, Theorem 2.3 and Appendix G.
-/

namespace HeytingLean
namespace Categorical

/-- A `MonadAlgebra` is a nucleus operator viewed through the categorical lens.
    This is a documentation alias that makes the CDL correspondence explicit.

    In CDL terminology:
    - The carrier type `L` is the algebra object
    - The nucleus `R` is the algebra structure map `a : T(A) → A`
    - Idempotence corresponds to the multiplication coherence
    - Extensive property corresponds to the unit law
    - Meet-preservation corresponds to strength -/
abbrev MonadAlgebra (L : Type*) [SemilatticeInf L] [OrderBot L] :=
  Core.Nucleus L

namespace MonadAlgebra

variable {L : Type*} [SemilatticeInf L] [OrderBot L]

/-- The monad multiplication coherence: R ∘ R = R.

    In CDL: This corresponds to the equation `a ∘ μ_A = a ∘ T(a)` where
    μ is the monad multiplication. For idempotent monads (nuclei), this
    simplifies to R(R(x)) = R(x).

    Reference: CDL Theorem 2.3, condition (ii). -/
theorem monad_multiplication (T : MonadAlgebra L) :
    T.R ∘ T.R = T.R :=
  funext T.idempotent

/-- The monad unit law: x ≤ T(x).

    In CDL: This corresponds to the equation `a ∘ η_A = id_A` where η is
    the monad unit. For nuclei (closure operators), the unit is inflationary:
    the identity embeds into the closed elements.

    Reference: CDL Theorem 2.3, condition (i). -/
theorem monad_unit (T : MonadAlgebra L) (x : L) :
    x ≤ T.R x :=
  T.extensive x

/-- The strong monad strength: T preserves meets.

    In CDL: This corresponds to the strength natural transformation
    σ_{A,B} : A × T(B) → T(A × B). For lattices, the product is the meet,
    and preservation of meets is exactly the strength condition.

    Reference: CDL Appendix G.5, strength for monoidal closed categories. -/
theorem monad_strength (T : MonadAlgebra L) (x y : L) :
    T.R (x ⊓ y) = T.R x ⊓ T.R y :=
  T.meet_preserving x y

/-- The fixed points of a monad algebra form the Eilenberg-Moore category.

    Elements x with T.R x = x are the "free T-algebras" - the image of the
    forgetful functor from T-Alg to the base category. -/
def fixedPointsSet (T : MonadAlgebra L) : Set L :=
  T.fixedPoints

/-- Every element in the image of R is a fixed point (Eilenberg-Moore object). -/
theorem image_subset_fixed (T : MonadAlgebra L) (a : L) :
    T.R a ∈ T.fixedPoints :=
  T.R_mem_fixedPoints a

/-- Fixed points are closed under meets (the Eilenberg-Moore category has products). -/
theorem fixed_closed_meet (T : MonadAlgebra L)
    {a b : L} (ha : a ∈ T.fixedPoints) (hb : b ∈ T.fixedPoints) :
    a ⊓ b ∈ T.fixedPoints :=
  T.fixedPoints_closed_inf ha hb

end MonadAlgebra

/-! ## Example: ReLU Nucleus as Monad Algebra

The ReLU nucleus on `Fin n → ℝ` is a canonical example. However, to construct
a `Core.Nucleus`, we need `OrderBot`, which `Fin n → ℝ` doesn't have by default.

The existing `Eigen.reluNucleus` uses Mathlib's `Nucleus` type which has
slightly different requirements. We document the correspondence here but
defer the full integration to a separate module.

**Key insight**: The algebraic properties (idempotent, inflationary, meet-preserving)
are the same regardless of the specific type class used.
-/

/-- The ReLU function is idempotent: `relu(relu(x)) = relu(x)`.
    This is the monad multiplication property. -/
theorem relu_idempotent (x : ℝ) : Eigen.relu (Eigen.relu x) = Eigen.relu x := by
  simp [Eigen.relu]

/-- The ReLU function is inflationary: `x ≤ relu(x)`.
    This is the monad unit property. -/
theorem relu_inflationary (x : ℝ) : x ≤ Eigen.relu x := by
  simp only [Eigen.relu, le_max_iff]
  left
  rfl

/-- The componentwise ReLU preserves the nucleus properties at each index.

    The full `reluNucleus n` uses Mathlib's `Nucleus` type, which captures
    the same algebraic structure as `Core.Nucleus` but with different
    type class requirements. -/
theorem reluNucleus_is_monad_algebra (n : Nat) :
    let T := Eigen.reluNucleus n
    (∀ v, T (T v) = T v) ∧
    (∀ v, v ≤ T v) ∧
    (∀ v w, T (v ⊓ w) = T v ⊓ T w) := by
  constructor
  · exact Eigen.reluNucleus_idempotent n
  constructor
  · exact Eigen.reluNucleus_le_apply n
  · exact Eigen.reluNucleus_map_inf n

end Categorical
end HeytingLean
