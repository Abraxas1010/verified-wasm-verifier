import HeytingLean.Logic.StageSemantics

/-
# Computability Logic: Parallel vs Choice (skeleton)

Defines tiny typeclasses for parallel (do both) and choice (pick one)
connectives on Ω and staged transports across a Bridge. Laws and concrete
instances are left to lenses that provide Ω.
-/

namespace HeytingLean
namespace Logic
namespace Computability

universe u

class ParallelCore (Ω : Type u) where
  pand : Ω → Ω → Ω
  por  : Ω → Ω → Ω

class ChoiceCore (Ω : Type u) where
  uchoice : Ω → Ω → Ω  -- environment chooses (⊔-like)
  tchoice : Ω → Ω → Ω  -- machine chooses (⊓-like)

-- Staged transports live under the global Stage namespace

end Computability
end Logic
end HeytingLean

namespace HeytingLean.Logic.Stage
universe u
variable {α Ω : Type u} [LE α] [LE Ω]

/-- Transport parallel-and across a bridge. -/
def Bridge.stagePand [HeytingLean.Logic.Computability.ParallelCore Ω]
    (B : Bridge α Ω) (x y : α) : α :=
  B.lift (HeytingLean.Logic.Computability.ParallelCore.pand (B.shadow x) (B.shadow y))

/-- Transport parallel-or across a bridge. -/
def Bridge.stagePor [HeytingLean.Logic.Computability.ParallelCore Ω]
    (B : Bridge α Ω) (x y : α) : α :=
  B.lift (HeytingLean.Logic.Computability.ParallelCore.por (B.shadow x) (B.shadow y))

/-- Transport choice-u across a bridge. -/
def Bridge.stageU [HeytingLean.Logic.Computability.ChoiceCore Ω]
    (B : Bridge α Ω) (x y : α) : α :=
  B.lift (HeytingLean.Logic.Computability.ChoiceCore.uchoice (B.shadow x) (B.shadow y))

/-- Transport choice-t across a bridge. -/
def Bridge.stageT [HeytingLean.Logic.Computability.ChoiceCore Ω]
    (B : Bridge α Ω) (x y : α) : α :=
  B.lift (HeytingLean.Logic.Computability.ChoiceCore.tchoice (B.shadow x) (B.shadow y))

@[simp] theorem Bridge.shadow_stagePand
    [HeytingLean.Logic.Computability.ParallelCore Ω]
    (B : Bridge α Ω) (x y : α) :
    B.shadow (B.stagePand x y) =
      HeytingLean.Logic.Computability.ParallelCore.pand (B.shadow x) (B.shadow y) := by
  unfold Bridge.stagePand; exact B.rt₁ _

@[simp] theorem Bridge.shadow_stagePor
    [HeytingLean.Logic.Computability.ParallelCore Ω]
    (B : Bridge α Ω) (x y : α) :
    B.shadow (B.stagePor x y) =
      HeytingLean.Logic.Computability.ParallelCore.por (B.shadow x) (B.shadow y) := by
  unfold Bridge.stagePor; exact B.rt₁ _

@[simp] theorem Bridge.shadow_stageU
    [HeytingLean.Logic.Computability.ChoiceCore Ω]
    (B : Bridge α Ω) (x y : α) :
    B.shadow (B.stageU x y) =
      HeytingLean.Logic.Computability.ChoiceCore.uchoice (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageU; exact B.rt₁ _

@[simp] theorem Bridge.shadow_stageT
    [HeytingLean.Logic.Computability.ChoiceCore Ω]
    (B : Bridge α Ω) (x y : α) :
    B.shadow (B.stageT x y) =
      HeytingLean.Logic.Computability.ChoiceCore.tchoice (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageT; exact B.rt₁ _

end HeytingLean.Logic.Stage
