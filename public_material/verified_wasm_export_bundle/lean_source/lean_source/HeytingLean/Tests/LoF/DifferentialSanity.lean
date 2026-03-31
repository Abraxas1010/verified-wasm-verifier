import HeytingLean.LoF.Combinators.Differential

/-!
Compile-only sanity checks for the Differential (DiLL-style) combinator slice.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential

#check (FormalSum Rat)
#check (FormalSum.app (K := Rat))
#check (FormalSum.appBilin (K := Rat))
#check (FormalSum.stepSum (K := Rat))
#check Loss.IOExample
#check GD.synthesize
#check Exp.codereliction_is_derivative
#check YDerivativeWitness

-- Application on singleton basis vectors behaves as expected.
example :
    (FormalSum.app (K := Rat) (single (K := Rat) Comb.K) (single (K := Rat) Comb.S)) =
      single (K := Rat) (Comb.app Comb.K Comb.S) := by
  simp

-- Exponential: degree-1 projection + embedding.
example :
    (Exp.dereliction (K := Rat) (V := FormalSum Rat)).comp (Exp.codereliction (K := Rat) (V := FormalSum Rat)) =
      LinearMap.id := by
  ext v
  simp [Exp.dereliction, Exp.codereliction]

-- Compute backend exists (for executables).
#check (HeytingLean.LoF.Combinators.Differential.Compute.FSum)

end LoF
end Tests
end HeytingLean
