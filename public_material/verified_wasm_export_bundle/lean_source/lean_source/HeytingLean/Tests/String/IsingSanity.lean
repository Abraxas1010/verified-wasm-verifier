import HeytingLean.Physics.String.ComplexF
import HeytingLean.Physics.String.Examples.Ising

/-
Compile-only: light sanity on Ising S/T applications (no numeric proofs).
-/

namespace HeytingLean
namespace Tests
namespace String

open HeytingLean.Physics.String
open HeytingLean.Physics.String.Examples.Ising

def basis0 : Vec3 := #[{re := 1.0, im := 0.0}, {re := 0.0, im := 0.0}, {re := 0.0, im := 0.0}]
def afterSTS : Vec3 := applyS (applyT (applyS basis0))

end String
end Tests
end HeytingLean

