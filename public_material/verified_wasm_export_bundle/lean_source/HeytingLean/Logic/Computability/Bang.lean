import HeytingLean.Logic.StageSemantics

/-
# Computability Logic: Bang (skeleton)

Minimal `!` operator as a core combinator with staged transport. Concrete
laws and instances are lens-specific and intentionally omitted here.
-/

namespace HeytingLean
namespace Logic
namespace Computability

universe u

class BangCore (Ω : Type u) where
  bang : Ω → Ω

end Computability
end Logic
end HeytingLean

namespace HeytingLean.Logic.Stage
universe u
variable {α Ω : Type u} [LE α] [LE Ω]

/-- Transport `!` across a bridge. -/
def Bridge.stageBang [HeytingLean.Logic.Computability.BangCore Ω]
    (B : Bridge α Ω) (x : α) : α :=
  B.lift (HeytingLean.Logic.Computability.BangCore.bang (B.shadow x))

@[simp] theorem Bridge.shadow_stageBang
    [HeytingLean.Logic.Computability.BangCore Ω]
    (B : Bridge α Ω) (x : α) :
    B.shadow (B.stageBang x) =
      HeytingLean.Logic.Computability.BangCore.bang (B.shadow x) := by
  unfold Bridge.stageBang; exact B.rt₁ _

end HeytingLean.Logic.Stage
