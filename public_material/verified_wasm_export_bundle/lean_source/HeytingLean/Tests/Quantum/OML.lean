import HeytingLean.Logic.StageSemantics
import HeytingLean.Logic.StageOML
import HeytingLean.Logic.OmegaLT
import HeytingLean.Quantum.Facade

/-
Compile-only sanity: staged OML ops and LT-lifted connectives.
-/

namespace HeytingLean
namespace Tests
namespace Quantum

open HeytingLean.Logic
open HeytingLean.Logic.Stage

universe u

section Generic
variable {α Ω : Type u} [LE α] [LE Ω]
variable [Stage.OmlCore Ω] [HeytingAlgebra Ω]

variable (B : Stage.Bridge α Ω)
variable (L : OmegaLT.LTCore Ω)
variable (x y : α)

def _omlMeet : α := (HeytingLean.Logic.Stage.Bridge.stageOmlMeet (B := B) x y)
def _omlJoin : α := (HeytingLean.Logic.Stage.Bridge.stageOmlJoin (B := B) x y)
def _omlCompl : α := (HeytingLean.Logic.Stage.Bridge.stageOmlCompl (B := B) x)

def _facade : HeytingLean.Quantum.Facade Ω := { lt := L }
def _qlJoin (a b : Ω) : Ω := (_facade (Ω := Ω) (L := L)).qJoin a b

end Generic

end Quantum
end Tests
end HeytingLean
