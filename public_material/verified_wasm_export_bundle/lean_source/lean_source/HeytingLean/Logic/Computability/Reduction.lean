import HeytingLean.Logic.StageSemantics

/-
# Computability Logic: Reduction (skeleton)

Provides a light "resource reduction" connective expressed as a collapsed
implication `¬A ∨ B` on a Heyting carrier, abstracted via a collapse
operator `κ : Ω → Ω` (e.g., a nucleus/reentry on Ω).
-/

namespace HeytingLean
namespace Logic
namespace Computability

universe u

variable {Ω : Type u}

section Heyting
variable [HeytingAlgebra Ω]

/-- Heyting-style negation. -/
@[simp] def hnot (a : Ω) : Ω := a ⇨ ⊥

/-- Collapse an implication-like reduction under a provided collapse operator. -/
@[simp] def reduces (κ : Ω → Ω) (a b : Ω) : Ω :=
  κ (hnot (Ω := Ω) a ⊔ b)

end Heyting

end Computability
end Logic
end HeytingLean

namespace HeytingLean.Logic.Stage
universe u
variable {α Ω : Type u} [LE α] [LE Ω]

/-- Transport a reduction expressed at Ω across a bridge by collapsing
on Ω first and then lifting back to α. -/
def Bridge.stageReduces [HeytingAlgebra Ω]
    (B : Bridge α Ω) (κ : Ω → Ω) (x y : α) : α :=
  B.lift (HeytingLean.Logic.Computability.reduces (Ω := Ω) κ (B.shadow x) (B.shadow y))

@[simp] theorem Bridge.shadow_stageReduces [HeytingAlgebra Ω]
    (B : Bridge α Ω) (κ : Ω → Ω) (x y : α) :
    B.shadow (B.stageReduces κ x y) =
      HeytingLean.Logic.Computability.reduces (Ω := Ω) κ (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageReduces; exact B.rt₁ _

end HeytingLean.Logic.Stage
