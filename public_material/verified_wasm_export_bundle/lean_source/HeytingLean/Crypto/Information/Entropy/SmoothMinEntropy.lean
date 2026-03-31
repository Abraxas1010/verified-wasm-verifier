import Mathlib.Data.Real.Basic
import HeytingLean.Crypto.Information.Entropy.MinEntropy

/-!
# Smooth Min-Entropy (interface-first)

We keep smoothing purely parametric: this file introduces the carrier structure and basic
well-formedness constraints on `ε`.
-/

namespace HeytingLean
namespace Crypto
namespace Information
namespace Entropy

open HeytingLean.Crypto.Information.Entropy

/-- Smooth min-entropy: `H^ε_min(X)` (interface carrier). -/
structure SmoothMinEntropy (α : Type*) [MinEntropySpace α] where
  /-- Smoothing parameter `ε`. -/
  smoothing : ℝ
  smoothing_nonneg : 0 ≤ smoothing
  smoothing_lt_one : smoothing < 1
  /-- The (smoothed) min-entropy value (in bits). -/
  value : ℝ

end Entropy
end Information
end Crypto
end HeytingLean

