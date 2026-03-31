import Mathlib.Algebra.Algebra.Basic
import HeytingLean.Chem.QED.Minkowski

/-!
# Spinors and gamma-matrix (Clifford) interface

We represent "gamma matrices" abstractly as elements of an algebra `A` over a commutative ring `𝕜`,
subject to the Clifford anticommutation relation with respect to a metric `eta`.

This is intentionally an interface (a structure of assumptions), not a concrete representation.
-/

namespace HeytingLean
namespace Chem
namespace QED

universe u

/-- A Clifford/gamma representation: `gamma : μ -> A` satisfying the anticommutation relation.

The relation is stated in an algebra `A` over `𝕜` using `algebraMap` for scalars. -/
class CliffordRep (𝕜 : Type u) (μ : Type u) (A : Type u) [CommRing 𝕜] [Ring A] [Algebra 𝕜 A]
    [HasMetric 𝕜 μ] where
  gamma : μ → A
  clifford_rel :
      ∀ μ₁ μ₂ : μ,
        gamma μ₁ * gamma μ₂ + gamma μ₂ * gamma μ₁
          = algebraMap 𝕜 A (2 * HasMetric.eta (𝕜 := 𝕜) μ₁ μ₂)

end QED
end Chem
end HeytingLean

