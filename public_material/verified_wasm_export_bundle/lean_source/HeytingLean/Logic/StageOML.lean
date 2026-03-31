import HeytingLean.Logic.StageSemantics

/-
Convenience stage wrappers for orthomodular operations over a bridge.
We reuse `OmlCore Ω` from StageSemantics.
-/

namespace HeytingLean
namespace Logic
open HeytingLean.Logic.Stage

universe u

namespace Stage

variable {α Ω : Type u} [LE α] [LE Ω] [OmlCore Ω]

def Bridge.stageOmlMeet (B : Bridge α Ω) (x y : α) : α :=
  B.lift (Stage.OmlCore.meet (B.shadow x) (B.shadow y))

def Bridge.stageOmlJoin (B : Bridge α Ω) (x y : α) : α :=
  B.lift (Stage.OmlCore.join (B.shadow x) (B.shadow y))

def Bridge.stageOmlCompl (B : Bridge α Ω) (x : α) : α :=
  B.lift (Stage.OmlCore.compl (B.shadow x))

@[simp] theorem Bridge.shadow_stageOmlMeet (B : Bridge α Ω) (x y : α) :
  B.shadow (B.stageOmlMeet x y) = Stage.OmlCore.meet (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageOmlMeet; exact B.rt₁ _

@[simp] theorem Bridge.shadow_stageOmlJoin (B : Bridge α Ω) (x y : α) :
  B.shadow (B.stageOmlJoin x y) = Stage.OmlCore.join (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageOmlJoin; exact B.rt₁ _

@[simp] theorem Bridge.shadow_stageOmlCompl (B : Bridge α Ω) (x : α) :
  B.shadow (B.stageOmlCompl x) = Stage.OmlCore.compl (B.shadow x) := by
  unfold Bridge.stageOmlCompl; exact B.rt₁ _

end Stage
end Logic
end HeytingLean
