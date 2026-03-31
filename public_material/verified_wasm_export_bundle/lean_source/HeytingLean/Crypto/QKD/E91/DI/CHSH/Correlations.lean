import Mathlib.Data.Real.Basic

/-!
# CHSH correlations (interface-first)

This directory implements a lightweight, CT-compatible device-independent layer for E91.
We start from *correlators* `E(x,y) ∈ [-1,1]` (expectation values), and define the
CHSH quantity:

`S = E(0,0) + E(0,1) + E(1,0) - E(1,1)`.

We avoid full probability/measure theory. A `CorrelationBox` can be added later as a
distributional refinement.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91
namespace DI
namespace CHSH

/-- Binary measurement settings. -/
abbrev Setting : Type := Bool

/-- A correlator box `E(x,y)`. -/
structure Correlator where
  E : Setting → Setting → ℝ
  bounded : ∀ x y, (-1 : ℝ) ≤ E x y ∧ E x y ≤ 1

/-- CHSH quantity `S = E(0,0) + E(0,1) + E(1,0) - E(1,1)`. -/
def chshQuantity (C : Correlator) : ℝ :=
  C.E false false + C.E false true + C.E true false - C.E true true

end CHSH
end DI
end E91
end QKD
end Crypto
end HeytingLean

