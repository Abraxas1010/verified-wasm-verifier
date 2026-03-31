import Mathlib.Algebra.Algebra.Basic

/-!
# Minkowski signature interface

We keep this abstract: chemistry/QED modules will depend on a "spacetime index" type and a metric
signature, but we do not commit to a concrete model at M0.
-/

namespace HeytingLean
namespace Chem
namespace QED

universe u

/-- A minimal interface for a (possibly Minkowski) bilinear form `eta` on an index type `μ`. -/
class HasMetric (𝕜 : Type u) (μ : Type u) where
  eta : μ → μ → 𝕜

end QED
end Chem
end HeytingLean

