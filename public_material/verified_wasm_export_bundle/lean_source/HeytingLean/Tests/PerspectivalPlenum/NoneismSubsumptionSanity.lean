import HeytingLean.PerspectivalPlenum.Subsumption
import HeytingLean.PerspectivalPlenum.Lens.Examples.SquareCircle

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open Noneism
open HeytingLean.PerspectivalPlenum

inductive Atom where
  | p
  deriving DecidableEq, Repr

def euclideanAdapter : Subsumption.NoneismLensAdapter Atom :=
  { lens :=
      { profile := Lens.Examples.euclideanProfile
        witness := fun _ => True
        contradicts := fun
          | .bot => True
          | _ => False } }

def higherDimAdapter : Subsumption.NoneismLensAdapter Atom :=
  { lens :=
      { profile := Lens.Examples.higherDimProfile
        witness := fun _ => True
        contradicts := fun
          | .bot => True
          | _ => False } }

#check Subsumption.NoneismLensAdapter
#check Subsumption.DerivabilityBridge

example : euclideanAdapter.interpretedClaim (.eExists (.var 0) : Formula Atom) := by
  simp [Subsumption.NoneismLensAdapter.interpretedClaim,
    Lens.LocallySatisfiable, euclideanAdapter]

example : euclideanAdapter.interpretedImpossible (.bot : Formula Atom) := by
  refine Lens.collapse_of_strict_contradiction euclideanAdapter.lens (.bot : Formula Atom) ?_ ?_ ?_
  · simp [euclideanAdapter, Lens.Examples.euclideanProfile, Lens.allowsContradictions]
  · simp [euclideanAdapter]
  · simp [euclideanAdapter]

example :
    euclideanAdapter.interpretedImpossible (.bot : Formula Atom)
      ∧ higherDimAdapter.interpretedClaim (.bot : Formula Atom) := by
  exact Subsumption.NoneismLensAdapter.collapse_is_lens_relative
    euclideanAdapter higherDimAdapter (.bot : Formula Atom)
    (by simp [euclideanAdapter, Lens.Examples.euclideanProfile, Lens.allowsContradictions])
    (by simp [euclideanAdapter])
    (by simp [euclideanAdapter])
    (by simp [higherDimAdapter])
    (by simp [higherDimAdapter, Lens.Examples.higherDimProfile, Lens.allowsContradictions])

end PerspectivalPlenum
end Tests
end HeytingLean
