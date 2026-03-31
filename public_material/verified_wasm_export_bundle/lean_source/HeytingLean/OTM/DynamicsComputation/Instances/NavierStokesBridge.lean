import HeytingLean.MirandaDynamics.External.Interfaces
import HeytingLean.OTM.DynamicsComputation.NucleusFromDynamics

namespace HeytingLean
namespace OTM
namespace DynamicsComputation
namespace Instances

universe u

/--
Interface package for Navier-Stokes computational universality assumptions.
This module is intentionally assumption-packaging only; geometric/PDE proofs
remain external and are represented explicitly as fields.
-/
structure NavierStokesUniversalityWitness (Phase : Type u) where
  flow : Nat → Phase → Phase
  flow_zero : ∀ x : Phase, flow 0 x = x
  flow_add : ∀ m n x, flow (m + n) x = flow m (flow n x)
  hasExternalConstruction : Prop

def NavierStokesUniversalityWitness.toDynamics
    {Phase : Type u} (W : NavierStokesUniversalityWitness Phase) :
    DynamicalSystem Phase where
  flow := W.flow
  flow_zero := W.flow_zero
  flow_add := W.flow_add

/--
Even in interface-only mode, the Navier-Stokes lane gets a formal nucleus object
from the induced dynamics.
-/
def navierStokesDynamicsNucleusInstance
    {Phase : Type u} (W : NavierStokesUniversalityWitness Phase) :
    DynamicsNucleusInstance Phase :=
  mkEquilibriumInstance W.toDynamics

end Instances
end DynamicsComputation
end OTM
end HeytingLean
