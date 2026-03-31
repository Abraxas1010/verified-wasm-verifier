import HeytingLean.Security.Composable.IdealFunctionality

/-!
# Ideal functionalities (interface-first): key exchange

This is intentionally lightweight: we do not model randomness here.
-/

namespace HeytingLean
namespace Security
namespace Composable
namespace Instances

open HeytingLean.Security.Composable

/-- Ideal key exchange functionality `F_KE`. -/
def IdealKeyExchange (keyLen : Nat) : IdealFunctionality where
  Input := Unit
  Output := Fin keyLen → Bool
  Leakage := Unit
  compute := fun _ => (fun _ => false, ())

end Instances
end Composable
end Security
end HeytingLean

