import HeytingLean.Logic.StageSemantics
import HeytingLean.Logic.Computability.UniformValidity
import HeytingLean.Logic.Computability.ChoiceParallel
import HeytingLean.Logic.Computability.Bang
import HeytingLean.Logic.Computability.Reduction

/-
Compile-only sanity checks for the CL skeletons. We avoid picking any
concrete Ω to keep dependencies light; the goal is to ensure staged
signatures line up and simp lemmas are usable.
-/

namespace HeytingLean
namespace Tests
namespace CL

open HeytingLean.Logic
open HeytingLean.Logic.Stage

universe u

section Generic
variable {α Ω : Type u} [LE α] [LE Ω]

variable (B : Stage.Bridge α Ω)

-- Typeclass hooks; downstream lenses may provide instances.
variable [Computability.ParallelCore Ω]
variable [Computability.ChoiceCore Ω]
variable [Computability.BangCore Ω]

variable (x y : α)

-- Ensure staged operators are available.
def _stagePandDemo : α := B.stagePand x y
def _stagePorDemo  : α := B.stagePor x y
def _stageUDemo    : α := B.stageU x y
def _stageTDemo    : α := B.stageT x y
def _stageBangDemo : α := B.stageBang x

-- Uniform validity alias typechecks.
def _uvAlias (z : α) : Prop :=
  Computability.UniformlyValidα (B := B) z

-- Transport lemma sanity: uv_lift_iff compiles and simplifies
/-- Transport lemma alias: uniform validity is preserved and reflected
through `lift`/`shadow`. This is a direct use of `uv_lift_iff`. -/
def _uvLift (u : Ω) :
    Computability.UniformlyValidα (B := B) (B.lift u) ↔
      Computability.UniformlyValid u :=
  Computability.Transport.uv_lift_iff (B := B) u

end Generic

end CL
end Tests
end HeytingLean
