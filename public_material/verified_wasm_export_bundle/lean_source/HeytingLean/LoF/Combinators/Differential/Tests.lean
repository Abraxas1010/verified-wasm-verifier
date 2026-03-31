import HeytingLean.LoF.Combinators.Differential.Codereliction
import HeytingLean.LoF.Combinators.Differential.GradientDescent
import HeytingLean.LoF.Combinators.Differential.SKYDerivatives

/-!
# Differential combinators: compile-time tests

This module is intentionally lightweight: it provides a few `#check`s and small `example`s to keep
the Differential slice honest under elaboration.
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential
namespace Tests

open scoped BigOperators

-- Exponential sanity: degree-1 projection after codereliction is identity.
example :
    (Exp.dereliction (K := Rat) (V := FormalSum Rat)).comp (Exp.codereliction (K := Rat) (V := FormalSum Rat)) =
      LinearMap.id := by
  ext v
  simp [Exp.dereliction, Exp.codereliction]

-- Loss/gradient APIs typecheck.
#check Loss.IOExample
#check Loss.totalLoss
#check GD.synthesize

-- Y-derivative witness exists when `f = 0` (trivial right inverse = id).
section

variable {K : Type*} [CommRing K]

example : Y_derivative_exists (K := K) (0 : FormalSum K) := by
  refine ⟨LinearMap.id, ?_⟩
  simp [derivativeApp2]

end

end Tests
end Differential
end Combinators
end LoF
end HeytingLean
