import Mathlib.Data.Real.Basic
import HeytingLean.Crypto.Information.Entropy.MinEntropy

/-!
# Conditional Min-Entropy (interface-first)

We treat conditional min-entropy as an abstract quantity `H_min(X|E)` with a single interface law:
conditioning does not increase entropy.
-/

namespace HeytingLean
namespace Crypto
namespace Information
namespace Entropy

open HeytingLean.Crypto.Information.Entropy

/-- Conditional min-entropy `H_min(X|E)` against an adversary system `E`. -/
structure ConditionalMinEntropy (X E : Type*) [MinEntropySpace X] where
  /-- Conditional entropy value associated to an `X`-distribution and an `E`-state. -/
  condHmin : MinEntropySpace.Dist (α := X) → E → ℝ
  /-- Conditioning decreases entropy (interface law). -/
  conditioning_decreases :
    ∀ (d : MinEntropySpace.Dist (α := X)) (e : E), condHmin d e ≤ MinEntropySpace.Hmin d

end Entropy
end Information
end Crypto
end HeytingLean

