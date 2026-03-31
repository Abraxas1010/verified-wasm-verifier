import HeytingLean.PerspectivalPlenum

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open HeytingLean.PerspectivalPlenum
open ContextualityEngine

#check VirtualObstructionBridge.virtualObstructionClass
#check VirtualObstructionBridge.virtualObstructionClass_void
#check VirtualObstructionBridge.virtualObstructionClass_life
#check VirtualObstructionBridge.virtualObstructionDegree_life
#check ProjectionObligations.virtual_life_obstruction_hook

inductive ToySource
  | void
  | life
  deriving DecidableEq

def toyProfile : VirtualObstructionBridge.VirtualProfile ToySource :=
  { stabilizes := fun g => g = .void
    void := .void
    life := .life
    void_stable := by simp
    life_unstable := by simp }

example :
    VirtualObstructionBridge.virtualObstructionClass toyProfile toyProfile.void =
      CechObstructionClass.none := by
  exact VirtualObstructionBridge.virtualObstructionClass_void toyProfile

example :
    VirtualObstructionBridge.virtualObstructionClass toyProfile toyProfile.life =
      CechObstructionClass.h1_overlap_incompatibility := by
  exact VirtualObstructionBridge.virtualObstructionClass_life toyProfile

example :
    cohomologyDegree (VirtualObstructionBridge.virtualObstructionClass toyProfile toyProfile.life) = 1 := by
  exact VirtualObstructionBridge.virtualObstructionDegree_life toyProfile

example :
    ProjectionObligations.keyName ProjectionObligations.ObligationKey.virtualLifeObstruction =
      "virtual_life_obstruction" := rfl

end PerspectivalPlenum
end Tests
end HeytingLean
