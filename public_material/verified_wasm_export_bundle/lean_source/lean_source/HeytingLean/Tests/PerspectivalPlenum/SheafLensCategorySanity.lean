import HeytingLean.PerspectivalPlenum.SheafLensCategory

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

#check HeytingLean.PerspectivalPlenum.LensSheaf.LensObj
#check HeytingLean.PerspectivalPlenum.LensSheaf.LensHom
#check HeytingLean.PerspectivalPlenum.LensSheaf.LensPresheaf
#check HeytingLean.PerspectivalPlenum.LensSheaf.LensSiteCoverage
#check HeytingLean.PerspectivalPlenum.LensSheaf.LensSiteCoverage.toLocalOperator
#check HeytingLean.PerspectivalPlenum.LensSheaf.SheafificationPath
#check HeytingLean.PerspectivalPlenum.LensSheaf.witnessPresheaf
#check HeytingLean.PerspectivalPlenum.LensSheaf.witnessPresheaf_singleton_amalgamates
#check HeytingLean.PerspectivalPlenum.LensSheaf.pairCover
#check HeytingLean.PerspectivalPlenum.LensSheaf.witnessPresheaf_pair_amalgamates_of_eq
#check HeytingLean.PerspectivalPlenum.LensSheaf.witnessPresheaf_pair_amalgamation_unique
#check HeytingLean.PerspectivalPlenum.LensSheaf.ExistsInPlenum
#check HeytingLean.PerspectivalPlenum.LensSheaf.existsInPlenum_and_localCollapse

#check HeytingLean.PerspectivalPlenum.LensSheaf.Examples.higherToEuclidean
#check HeytingLean.PerspectivalPlenum.LensSheaf.Examples.euclideanSingletonFamily_glues

open HeytingLean.PerspectivalPlenum
open LensSheaf
open LensSheaf.Examples

def euclideanPairFamily :
    MatchingFamily ShapeWitnessPresheaf euclideanObj (pairCover euclideanObj) where
  sec
    | false => squareCircleSection
    | true => squareCircleSection

example :
    Amalgamates ShapeWitnessPresheaf euclideanObj (pairCover euclideanObj) euclideanPairFamily := by
  exact witnessPresheaf_pair_amalgamates_of_eq euclideanObj euclideanPairFamily rfl

example :
    ExistsInPlenum Lens.Examples.ShapeObject.squareCircle ∧
      Lens.CollapseToBottom Lens.Examples.euclideanLens Lens.Examples.ShapeObject.squareCircle := by
  refine ⟨?_, ?_⟩
  · exact existsInPlenum_of_localWitness ⟨Lens.Examples.higherDimLens⟩
      (by simp [Lens.Examples.higherDimLens])
  · exact (Lens.Examples.squareCircle_lens_relative).1

end PerspectivalPlenum
end Tests
end HeytingLean
