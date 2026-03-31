import HeytingLean.Security.Composable.Composition
import HeytingLean.Security.Composable.Instances.IdealKeyExchange

/-!
# UC tests (Phase 12)

Small compile-time checks for the Phase 2 UC scaffold.
-/

namespace HeytingLean.Tests.Security.UCTests

open HeytingLean.Security.Composable

example : IdealFunctionality :=
  Instances.IdealKeyExchange 32

end HeytingLean.Tests.Security.UCTests

