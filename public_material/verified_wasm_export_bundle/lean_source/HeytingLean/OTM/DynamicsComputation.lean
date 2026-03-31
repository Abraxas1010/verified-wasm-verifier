import HeytingLean.OTM.DynamicsComputation.DynamicalSystem
import HeytingLean.OTM.DynamicsComputation.NucleusFromDynamics
import HeytingLean.OTM.DynamicsComputation.StablePropositions
import HeytingLean.OTM.DynamicsComputation.ForwardCorrespondence
import HeytingLean.OTM.DynamicsComputation.ReverseCorrespondence
import HeytingLean.OTM.DynamicsComputation.RealizabilityBridge
import HeytingLean.OTM.DynamicsComputation.Instances.BilliardsBridge
import HeytingLean.OTM.DynamicsComputation.Instances.EulerBridge
import HeytingLean.OTM.DynamicsComputation.Instances.NavierStokesBridge
import HeytingLean.OTM.DynamicsComputation.Lens.DynamicsComputationLens
import HeytingLean.OTM.DynamicsComputation.MainTheorem
import HeytingLean.OTM.DynamicsComputation.IntegrationExamples
import HeytingLean.OTM.DynamicsComputation.TraceHarness

/-!
# OTM DynamicsComputation (umbrella)

This umbrella module collects the first complete, compile-checked milestone of the
Dynamics <-> Computation bridge:

- dynamics scaffolding and reachability/equilibrium constructions,
- nucleus extraction interfaces and canonical equilibrium nucleus,
- stable proposition transport via sublocales,
- forward/reverse correspondence interfaces,
- realizability bridge packaging,
- instance interfaces (billiards/euler/navier-stokes),
- lens transport and milestone theorem packaging.
-/
