import HeytingLean.PerspectivalPlenum.StrictRatchet.Core
import HeytingLean.PerspectivalPlenum.Lens.Examples.SquareCircle

namespace HeytingLean
namespace PerspectivalPlenum
namespace StrictRatchet

/--
Explicit separation witness by stage level.

`L2` carries the lens-relative square-circle witness; earlier stages do not.
This gives a concrete strictness witness without altering the legacy re-reentry tower.
-/
def separationWitness : StrictLevel → Prop
  | .L0 => False
  | .L1 => False
  | .L2 =>
      Lens.CollapseToBottom Lens.Examples.euclideanLens Lens.Examples.ShapeObject.squareCircle ∧
        Lens.LocallySatisfiable Lens.Examples.higherDimLens Lens.Examples.ShapeObject.squareCircle

@[simp] theorem separationWitness_L0 : ¬ separationWitness .L0 := by
  simp [separationWitness]

@[simp] theorem separationWitness_L1 : ¬ separationWitness .L1 := by
  simp [separationWitness]

theorem separationWitness_L2 : separationWitness .L2 :=
  Lens.Examples.squareCircle_lens_relative

theorem explicit_strict_separation :
    separationWitness .L2 ∧ ¬ separationWitness .L1 := by
  exact ⟨separationWitness_L2, separationWitness_L1⟩

namespace StrictStage

universe u
variable {α : Type u} [Order.Frame α]

/-- Stage-indexed view of the strict separation witness. -/
def hasSeparationWitness (S : StrictStage α) : Prop :=
  separationWitness S.level

theorem base_has_no_separationWitness (J : Nucleus α) :
    ¬ hasSeparationWitness (base J) := by
  simp [hasSeparationWitness, base, separationWitness]

theorem plenum_has_separationWitness (steps : List (RatchetStep α)) (J : Nucleus α) :
    hasSeparationWitness (plenum steps J) := by
  simpa [hasSeparationWitness, plenum] using separationWitness_L2

theorem strict_gap_base_to_plenum (steps : List (RatchetStep α)) (J : Nucleus α) :
    strictlyPrecedes (base J) (plenum steps J) ∧
      hasSeparationWitness (plenum steps J) ∧
      ¬ hasSeparationWitness (base J) := by
  refine ⟨StrictStage.base_strictly_precedes_plenum (steps := steps) (J := J), ?_, ?_⟩
  · exact plenum_has_separationWitness (steps := steps) (J := J)
  · exact base_has_no_separationWitness (J := J)

end StrictStage

end StrictRatchet
end PerspectivalPlenum
end HeytingLean
