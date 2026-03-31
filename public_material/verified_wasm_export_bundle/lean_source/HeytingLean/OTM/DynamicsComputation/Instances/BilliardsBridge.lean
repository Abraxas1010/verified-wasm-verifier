import HeytingLean.MirandaDynamics.Billiards.CantorNucleus
import HeytingLean.MirandaDynamics.FixedPoint.PeriodicNucleus
import HeytingLean.OTM.DynamicsComputation.NucleusFromDynamics

namespace HeytingLean
namespace OTM
namespace DynamicsComputation
namespace Instances

open Set

/-- Billiards lane: re-export the Cantor nucleus as a dynamics-computation instance. -/
def billiardsCantorNucleus : Nucleus (Set ℝ) :=
  MirandaDynamics.Billiards.cantorNucleus

theorem billiardsCantorNucleus_fixed_iff (U : Set ℝ) :
    billiardsCantorNucleus U = U ↔ MirandaDynamics.Billiards.cantorCompl ⊆ U := by
  simpa [billiardsCantorNucleus] using MirandaDynamics.Billiards.cantorNucleus_fixed_iff U

/-- Billiards lane: periodic-loop nucleus from the flow bridge. -/
def billiardsLoopNucleus (posTol dirCosTol : Float) : Nucleus (Set Bridges.FlowTraj) :=
  MirandaDynamics.FixedPoint.Flow.periodicNucleus posTol dirCosTol

theorem billiardsLoopNucleus_eq_flow (posTol dirCosTol : Float) :
    billiardsLoopNucleus posTol dirCosTol = Bridges.Flow.flowNucleusOsc posTol dirCosTol := by
  simpa [billiardsLoopNucleus] using
    MirandaDynamics.FixedPoint.Flow.periodicNucleus_eq_flowNucleusOsc posTol dirCosTol

end Instances
end DynamicsComputation
end OTM
end HeytingLean
