import HeytingLean.Logic.OmegaLT
import HeytingLean.Quantum.Facade
import HeytingLean.LoF.Nucleus

/-
Compile-only: build a Facade from a Reentry (j := R) abstractly and use lifted ops.
This avoids choosing a concrete Ω; it type-checks under the required classes.
-/

namespace HeytingLean
namespace Tests
namespace Quantum

open HeytingLean.Logic
open HeytingLean.Logic.OmegaLT

universe u

section Generic
variable {Ω : Type u} [LE Ω] [HeytingAlgebra Ω] [Logic.Stage.OmlCore Ω]
variable [LoF.PrimaryAlgebra Ω]

variable (R : LoF.Reentry Ω)
def facadeFromR : HeytingLean.Quantum.Facade Ω :=
  { lt := OmegaLT.ofReentryOmega (α := Ω) R }

variable (a b : Ω)
def _qJoinDemo : Ω := (facadeFromR (R := R)).qJoin a b

end Generic

end Quantum
end Tests
end HeytingLean

