import HeytingLean.HeytingVeil.Refinement.Core
import HeytingLean.HeytingVeil.ModelCheck.BFS

namespace HeytingLean
namespace HeytingVeil
namespace Refinement

open HeytingLean.HeytingVeil.ModelCheck

universe u v

def checkStutteringSimulation
    {SrcState : Type u} {TgtState : Type v}
    [DecidableEq SrcState] [DecidableEq TgtState]
    (dmSrc : DecidableMachine SrcState)
    (dmTgt : DecidableMachine TgtState)
    (encode : SrcState → TgtState)
    (bound : Nat) : Bool :=
  let srcReach := bfsReachable dmSrc bound
  let initOk :=
    srcReach.all (fun s =>
      if decide (dmSrc.machine.Init s) then
        decide (dmTgt.machine.Init (encode s))
      else
        true)
  let stepOk :=
    srcReach.all (fun s =>
      (successors dmSrc s).all (fun t =>
        haveI : Decidable (dmTgt.machine.Step (encode s) (encode t)) :=
          dmTgt.decStep (encode s) (encode t)
        decide (dmTgt.machine.Step (encode s) (encode t) ∨ encode s = encode t)))
  initOk && stepOk

end Refinement
end HeytingVeil
end HeytingLean
