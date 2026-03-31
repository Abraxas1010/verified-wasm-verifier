import HeytingLean.PerspectivalPlenum.Lens.Collapse

namespace HeytingLean
namespace PerspectivalPlenum
namespace Lens
namespace Examples

/-- Minimal object language for lens-relative impossibility demonstrations. -/
inductive ShapeObject where
  | square
  | circle
  | squareCircle
  deriving DecidableEq, Repr

/-- Strict Boolean/Euclidean lens profile. -/
def euclideanProfile : LensProfile :=
  { name := "Euclidean-2D"
    contradictionPolicy := ContradictionPolicy.booleanStrict
    dimension := 2
    languageTag := "classical-geometry"
    metricTag := "euclidean" }

/-- Higher-dimensional permissive lens profile. -/
def higherDimProfile : LensProfile :=
  { name := "HigherDim-Paraconsistent"
    contradictionPolicy := ContradictionPolicy.paraconsistent
    dimension := 4
    languageTag := "multi-geometry"
    metricTag := "mixed" }

/-- Euclidean lens: every shape is nameable, but square-circle is contradictory. -/
def euclideanLens : SemanticLens ShapeObject :=
  { profile := euclideanProfile
    witness := fun _ => True
    contradicts := fun x => x = ShapeObject.squareCircle }

/-- Higher-dimensional lens: contradiction can be admitted as a local object. -/
def higherDimLens : SemanticLens ShapeObject :=
  { profile := higherDimProfile
    witness := fun _ => True
    contradicts := fun x => x = ShapeObject.squareCircle }

@[simp] theorem squareCircle_contradictory_euclidean :
    euclideanLens.contradicts ShapeObject.squareCircle := by
  simp [euclideanLens]

@[simp] theorem squareCircle_contradictory_higherDim :
    higherDimLens.contradicts ShapeObject.squareCircle := by
  simp [higherDimLens]

/-- In strict Euclidean lens, square-circle collapses locally. -/
theorem squareCircle_collapses_in_euclidean :
    CollapseToBottom euclideanLens ShapeObject.squareCircle := by
  refine collapse_of_strict_contradiction euclideanLens ShapeObject.squareCircle ?_ ?_ ?_
  · simp [euclideanLens, euclideanProfile, allowsContradictions]
  · simp [euclideanLens]
  · simp [euclideanLens]

/-- In permissive higher-dimensional lens, square-circle is locally satisfiable. -/
theorem squareCircle_survives_in_higherDim :
    LocallySatisfiable higherDimLens ShapeObject.squareCircle := by
  refine satisfiable_of_allowed_contradiction higherDimLens ShapeObject.squareCircle ?_ ?_
  · simp [higherDimLens]
  · simp [higherDimLens, higherDimProfile, allowsContradictions]

/-- Lens-relative result: same object collapses in one lens and survives in another. -/
theorem squareCircle_lens_relative :
    CollapseToBottom euclideanLens ShapeObject.squareCircle
      ∧ LocallySatisfiable higherDimLens ShapeObject.squareCircle := by
  exact ⟨squareCircle_collapses_in_euclidean, squareCircle_survives_in_higherDim⟩

end Examples
end Lens
end PerspectivalPlenum
end HeytingLean
