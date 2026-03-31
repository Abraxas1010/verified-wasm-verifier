import HeytingLean.Logic.StageSemantics

/-
# Computability Logic: Uniform Validity (skeleton)

Minimal, compile-friendly definitions that integrate with the Stage/Bridge
transport. We model an "interpretation" as a wrapper that decides which
elements of Ω hold. Uniform validity then requires truth for all
interpretations.
-/

namespace HeytingLean
namespace Logic
namespace Computability

universe u

/-- A lightweight interpretation: tells which Ω-states hold. -/
structure Interpretation (Ω : Type u) where
  holds : Ω → Prop

namespace Interpretation
variable {Ω : Type u}

@[simp] def eval (I : Interpretation Ω) (a : Ω) : Prop :=
  I.holds a

end Interpretation

/-- Uniform validity: holds under every interpretation. -/
@[simp] def UniformlyValid {Ω : Type u} (a : Ω) : Prop :=
  ∀ I : Interpretation Ω, I.holds a

open HeytingLean.Logic.Stage

/-- Transport uniform validity through a bridge by viewing `x : α` as its
shadow in Ω. This is a mere alias to make call sites pleasant. -/
@[simp] def UniformlyValidα {α Ω : Type u} [LE α] [LE Ω]
    (B : Stage.Bridge α Ω) (x : α) : Prop :=
  UniformlyValid (B.shadow x)

/-! ### Transport invariance lemmas -/

namespace Transport
open HeytingLean.Logic.Stage

variable {α Ω : Type u} [LE α] [LE Ω]

/-- By definition, the α-alias is exactly validity of the shadow. -/
@[simp] theorem uv_alpha_def (B : Bridge α Ω) (x : α) :
    UniformlyValidα (B := B) x = UniformlyValid (B.shadow x) := rfl

/-- Uniform validity is preserved and reflected through `lift`/`shadow`. -/
@[simp] theorem uv_lift_iff (B : Bridge α Ω) (u : Ω) :
    UniformlyValidα (B := B) (B.lift u) ↔ UniformlyValid u := by
  -- expand the alias and rewrite via the round-trip `rt₁`.
  change UniformlyValid (B.shadow (B.lift u)) ↔ UniformlyValid u
  simp [B.rt₁]

@[simp] theorem uv_shadow_iff (B : Bridge α Ω) (x : α) :
    UniformlyValid (B.shadow x) ↔ UniformlyValidα (B := B) x := Iff.rfl

end Transport

end Computability
end Logic
end HeytingLean
