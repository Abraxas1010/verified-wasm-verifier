import HeytingLean.LoF.Combinators.Topos.Localization
import HeytingLean.LoF.Combinators.Topos.StepsSite

/-!
Compile-only sanity checks for Phase 4.3 (nucleus as localization/reflector).

We specialize to the SKY reachability site `StepsCat` with the dense topology and check that the
restricted closure map satisfies the expected universal property (Galois insertion).
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open Order
open HeytingLean.LoF.Combinators.Topos

variable {X : StepsCat}

#check closeRestrict (C := StepsCat) (J := stepsDenseTopology) X
#check closeGI (C := StepsCat) (J := stepsDenseTopology) X

example (S : Sieve X) (T : ClosedSieve (C := StepsCat) stepsDenseTopology X) :
    closeRestrict (C := StepsCat) (J := stepsDenseTopology) X S ≤ T ↔ S ≤ (T : Sieve X) := by
  simpa using
    (closeRestrict_le_iff (C := StepsCat) (J := stepsDenseTopology) (X := X) (S := S) (T := T))

end LoF
end Tests
end HeytingLean
