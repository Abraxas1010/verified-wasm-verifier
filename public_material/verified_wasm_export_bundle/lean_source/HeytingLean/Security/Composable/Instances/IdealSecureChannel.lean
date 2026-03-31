import HeytingLean.Security.Composable.IdealFunctionality

/-!
# Ideal functionalities (interface-first): secure channel
-/

namespace HeytingLean
namespace Security
namespace Composable
namespace Instances

open HeytingLean.Security.Composable

/-- Ideal secure channel functionality `F_SC`. -/
def IdealSecureChannel (msgLen : Nat) : IdealFunctionality where
  Input := Fin msgLen → Bool
  Output := Fin msgLen → Bool
  Leakage := Nat
  compute := fun m => (m, msgLen)

end Instances
end Composable
end Security
end HeytingLean

