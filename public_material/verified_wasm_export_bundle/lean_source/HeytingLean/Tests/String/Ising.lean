import HeytingLean.Physics.String.ComplexF
import HeytingLean.Physics.String.Examples.Ising

/-
Compile-only: build an Ising vector and apply S/T a few steps.
-/

namespace HeytingLean
namespace Tests
namespace String

open HeytingLean.Physics.String
open HeytingLean.Physics.String.Examples.Ising

def v0 : Vec3 := #[{re := 1.0, im := 0.0}, {re := 0.0, im := 0.0}, {re := 0.0, im := 0.0}]
def vS : Vec3 := applyS v0
def vT : Vec3 := applyT vS

end String
end Tests
end HeytingLean

