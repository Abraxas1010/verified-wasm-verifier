import HeytingLean.Logic.OmegaLT
import HeytingLean.Logic.StageLT
import HeytingLean.Logic.StageSemantics

/-
Compile-only sanity for Ω-level LT staged operations and Reentry adapter.
-/

namespace HeytingLean
namespace Tests
namespace LT

open HeytingLean.Logic
open HeytingLean.Logic.Stage

universe u

section Generic
variable {α Ω : Type u} [LE α] [LE Ω]
variable [HeytingAlgebra Ω]

variable (B : Stage.Bridge α Ω)
variable (L : Logic.OmegaLT.LTCore Ω)
variable (x y : α)

def _demoMeet : α := HeytingLean.Logic.Stage.Bridge.stageLTMeet (B := B) L x y
def _demoJoin : α := HeytingLean.Logic.Stage.Bridge.stageLTJoin (B := B) L x y
def _demoImp  : α := HeytingLean.Logic.Stage.Bridge.stageLTImp  (B := B) L x y
def _demoNeg  : α := HeytingLean.Logic.Stage.Bridge.stageLTNeg  (B := B) L x

end Generic

end LT
end Tests
end HeytingLean
