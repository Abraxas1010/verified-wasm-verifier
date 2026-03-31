import HeytingLean.PerspectivalPlenum.CechCohomology

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open HeytingLean.PerspectivalPlenum
open LensSheaf
open LensSheaf.Cech
open LensSheaf.Cech.True

#check OneSkeleton
#check Cech0
#check Cech1
#check d0
#check IsCoboundary
#check H1Class

#check pairOracle
#check True.Triangle.parityClass
#check True.Triangle.oracle
#check True.Triangle.oracle_surrogate_sound

example :
    ¬ IsCoboundary True.Triangle.skeleton True.Triangle.parityCocycle := by
  exact True.Triangle.parityCocycle_nonzero

example :
    ContextualityEngine.HasCechH1
      Quantum.Contextuality.Triangle.X
      Quantum.Contextuality.Triangle.cover
      Quantum.Contextuality.Triangle.model
      (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC) := by
  exact True.Triangle.oracle_surrogate_sound

example :
    ∃ _ : H1Class True.Triangle.skeleton, True := by
  exact True.Triangle.exists_nonzero_class

end PerspectivalPlenum
end Tests
end HeytingLean
