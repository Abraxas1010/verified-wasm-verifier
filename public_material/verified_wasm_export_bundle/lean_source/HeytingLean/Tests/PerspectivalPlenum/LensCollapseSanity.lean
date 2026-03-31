import HeytingLean.PerspectivalPlenum.Lens

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

#check HeytingLean.PerspectivalPlenum.Lens.ContradictionPolicy
#check HeytingLean.PerspectivalPlenum.Lens.SemanticLens
#check HeytingLean.PerspectivalPlenum.Lens.LocallySatisfiable
#check HeytingLean.PerspectivalPlenum.Lens.CollapseToBottom

#check HeytingLean.PerspectivalPlenum.Lens.lens_relative_collapse_and_survival
#check HeytingLean.PerspectivalPlenum.Lens.Examples.squareCircle_lens_relative

example :
    HeytingLean.PerspectivalPlenum.Lens.CollapseToBottom
      HeytingLean.PerspectivalPlenum.Lens.Examples.euclideanLens
      HeytingLean.PerspectivalPlenum.Lens.Examples.ShapeObject.squareCircle :=
  HeytingLean.PerspectivalPlenum.Lens.Examples.squareCircle_collapses_in_euclidean

example :
    HeytingLean.PerspectivalPlenum.Lens.LocallySatisfiable
      HeytingLean.PerspectivalPlenum.Lens.Examples.higherDimLens
      HeytingLean.PerspectivalPlenum.Lens.Examples.ShapeObject.squareCircle :=
  HeytingLean.PerspectivalPlenum.Lens.Examples.squareCircle_survives_in_higherDim

end PerspectivalPlenum
end Tests
end HeytingLean
