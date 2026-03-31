import HeytingLean.Security.Composable.IdealFunctionality

/-!
# Universal Composability (UC), interface-first: simulators

A simulator reconstructs a protocol transcript given only the ideal leakage.
-/

namespace HeytingLean
namespace Security
namespace Composable

universe u v w

/-- A simulator for protocol `π` with respect to ideal functionality `F`. -/
structure Simulator (F : IdealFunctionality.{u, v, w}) (π : Protocol F) where
  SimState : Type
  init : SimState
  simulate : F.Leakage → SimState → (π.Message × SimState)

end Composable
end Security
end HeytingLean

