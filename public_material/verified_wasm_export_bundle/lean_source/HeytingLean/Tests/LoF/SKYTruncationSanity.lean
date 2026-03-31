import HeytingLean.LoF.Combinators.Topos.Truncation
import HeytingLean.LoF.Combinators.Topos.StepsSite

/-!
Compile-only sanity checks for Phase 4.2 (closure-kernel quotient).

We check that quotienting `Sieve X` by the kernel of `J.close` produces the type of closed sieves.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Combinators.Topos

variable {X : StepsCat}

#check CloseQuot (C := StepsCat) (J := stepsDenseTopology) X
#check closeQuotEquivClosed (C := StepsCat) (J := stepsDenseTopology) X

noncomputable example :
    CloseQuot (C := StepsCat) (J := stepsDenseTopology) X ≃
      ClosedSieve (C := StepsCat) stepsDenseTopology X :=
  closeQuotEquivClosed (C := StepsCat) (J := stepsDenseTopology) X

end LoF
end Tests
end HeytingLean
