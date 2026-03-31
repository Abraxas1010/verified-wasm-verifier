import HeytingLean.Topology.Knot.Fixtures

/-!
# Sanity checks: Burau Alexander polynomial (closed braids)

These tests ensure the Burau-based Alexander computation matches a tiny fixture table.
The fixture expectations are normalized up to multiplication by units `±t^k`.
-/

namespace HeytingLean.Tests.Topology.BurauAlexanderSanity

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Fixtures

private def isOkEq (f : Fixtures.BraidFixture) : Bool :=
  match Fixtures.alexanderComputed f with
  | .ok p => decide (p = Fixtures.alexanderExpected f)
  | .error _ => false

example : (Fixtures.braidFixtures.all isOkEq) = true := by
  native_decide

end HeytingLean.Tests.Topology.BurauAlexanderSanity

