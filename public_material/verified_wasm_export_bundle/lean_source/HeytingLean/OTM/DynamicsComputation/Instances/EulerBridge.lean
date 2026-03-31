import HeytingLean.MirandaDynamics.Computation.TuringMachine
import HeytingLean.OTM.DynamicsComputation.NucleusFromDynamics

namespace HeytingLean
namespace OTM
namespace DynamicsComputation
namespace Instances

open HeytingLean.MirandaDynamics.Computation

universe u v

/--
Interface-first witness for the Euler universality lane.
This records exactly the data needed to connect an external construction
to the internal dynamics/computation bridge.
-/
structure EulerUniversalityWitness (Phase : Type u) (Cfg : Type v) where
  flow : Nat → Phase → Phase
  flow_zero : ∀ x : Phase, flow 0 x = x
  flow_add : ∀ m n x, flow (m + n) x = flow m (flow n x)
  encodeCfg : Cfg → Phase
  decodeCfg : Phase → Cfg
  simulates :
    ∀ (TM : HaltSys Cfg) (init : Cfg) (fuel : Nat),
      decodeCfg (flow fuel (encodeCfg init)) = TM.stepN fuel init

def EulerUniversalityWitness.toDynamics
    {Phase : Type u} {Cfg : Type v} (W : EulerUniversalityWitness Phase Cfg) :
    DynamicalSystem Phase where
  flow := W.flow
  flow_zero := W.flow_zero
  flow_add := W.flow_add

/--
Given an Euler universality witness, we obtain a canonical dynamics nucleus instance.
-/
def eulerDynamicsNucleusInstance
    {Phase : Type u} {Cfg : Type v} (W : EulerUniversalityWitness Phase Cfg) :
    DynamicsNucleusInstance Phase :=
  mkEquilibriumInstance W.toDynamics

end Instances
end DynamicsComputation
end OTM
end HeytingLean
