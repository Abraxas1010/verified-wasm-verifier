import HeytingLean.Logic.StageSemantics
import HeytingLean.Logic.OmegaLT

/-!
Stage transports for Ω-level LT operations over a `Bridge`.
This file defines `Bridge.stageLT{Meet,Join,Imp,Neg}` under
`HeytingLean.Logic.Stage` so field-notation and fully-qualified
names are consistent for tests and facades.
-/

namespace HeytingLean
namespace Logic
namespace Stage

open HeytingLean.Logic.OmegaLT

universe u

variable {α Ω : Type u} [LE α] [LE Ω] [HeytingAlgebra Ω]

def Bridge.stageLTMeet (B : Bridge α Ω) (_L : LTCore Ω) (x y : α) : α :=
  B.lift ((B.shadow x) ⊓ (B.shadow y))

def Bridge.stageLTJoin (B : Bridge α Ω) (L : LTCore Ω) (x y : α) : α :=
  B.lift (L.ltJoin (B.shadow x) (B.shadow y))

def Bridge.stageLTImp (B : Bridge α Ω) (L : LTCore Ω) (x y : α) : α :=
  B.lift (L.ltImp (B.shadow x) (B.shadow y))

def Bridge.stageLTNeg (B : Bridge α Ω) (L : LTCore Ω) (x : α) : α :=
  B.lift (L.ltNeg (B.shadow x))

@[simp] theorem Bridge.shadow_stageLTMeet (B : Bridge α Ω)
    (L : LTCore Ω) (x y : α) :
    B.shadow (B.stageLTMeet L x y) = B.shadow x ⊓ B.shadow y := by
  unfold Bridge.stageLTMeet; exact B.rt₁ _

@[simp] theorem Bridge.shadow_stageLTJoin (B : Bridge α Ω)
    (L : LTCore Ω) (x y : α) :
    B.shadow (B.stageLTJoin L x y) = L.ltJoin (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageLTJoin; exact B.rt₁ _

@[simp] theorem Bridge.shadow_stageLTImp (B : Bridge α Ω)
    (L : LTCore Ω) (x y : α) :
    B.shadow (B.stageLTImp L x y) = L.ltImp (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageLTImp; exact B.rt₁ _

@[simp] theorem Bridge.shadow_stageLTNeg (B : Bridge α Ω)
    (L : LTCore Ω) (x : α) :
    B.shadow (B.stageLTNeg L x) = L.ltNeg (B.shadow x) := by
  unfold Bridge.stageLTNeg; exact B.rt₁ _

end Stage
end Logic
end HeytingLean
