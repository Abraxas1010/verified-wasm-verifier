import HeytingLean.PerspectivalPlenum.CechObstruction

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open HeytingLean.PerspectivalPlenum
open LensSheaf
open LensSheaf.Cech
open ContextualityEngine

#check H0GlobalSections
#check HasH0
#check HasH1Obstruction
#check hasH0_iff_amalgamates
#check pairCompatible_hasH0
#check pairIncompatible_hasH1

#check CechObstructionClass
#check cohomologyDegree
#check HasCechH0
#check HasCechH1
#check triangle_has_cech_h1
#check triangleObstructionClass

example :
    cohomologyDegree triangleObstructionClass = 1 := by
  simpa using triangle_obstructionDegree

example :
    HasCechH1
      Quantum.Contextuality.Triangle.X
      Quantum.Contextuality.Triangle.cover
      Quantum.Contextuality.Triangle.model
      (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC) := by
  exact triangle_has_cech_h1

end PerspectivalPlenum
end Tests
end HeytingLean
