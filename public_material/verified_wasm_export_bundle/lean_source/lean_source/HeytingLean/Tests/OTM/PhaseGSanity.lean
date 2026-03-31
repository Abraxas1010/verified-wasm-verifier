import HeytingLean.OTM.IntegrationExamples
import HeytingLean.OTM.DynamicsComputation.Lens.DynamicsComputationLens

namespace HeytingLean.Tests.OTM

open HeytingLean.OTM

example (fuel : Nat) :
    otm_decode_cfg (Cfg := Nat)
        ((Machine.run fuel (otm_of_tm (Cfg := Nat) counterTM counterInit)).runtime.control) = fuel :=
  counter_example_decode_run fuel

example :
    otmHaltsAtFuel counterTM counterInit 2 :=
  counter_example_halts_at_two

example :
    ¬ otmHaltsAtFuel counterTM counterInit 1 :=
  counter_example_not_halts_at_one

example :
    preGameIndex Numbers.Surreal.TransfinitePreGame.PreGame.omega =
      Numbers.Ordinal.OrdinalCNF.omega :=
  surreal_index_micro_example

example :
    (∀ fuel,
      otm_decode_cfg (Cfg := Nat)
          ((Machine.run fuel (otm_of_tm (Cfg := Nat) counterTM counterInit)).runtime.control)
            = fuel) ∧
      otmHaltsAtFuel counterTM counterInit 2 ∧
      ¬ otmHaltsAtFuel counterTM counterInit 1 ∧
      preGameIndex Numbers.Surreal.TransfinitePreGame.PreGame.omega =
        Numbers.Ordinal.OrdinalCNF.omega :=
  otm_integration_examples_witness

end HeytingLean.Tests.OTM

namespace HeytingLean.Tests.OTM.DynamicsComputation

open HeytingLean.OTM.DynamicsComputation
open HeytingLean.OTM.DynamicsComputation.Lens

def natAddSystem : DynamicalSystem Nat where
  flow n x := n + x
  flow_zero := by intro x; simp
  flow_add := by
    intro m n x
    simp [Nat.add_assoc]

def natIdLens : DynamicsComputationLens Nat Nat where
  encode := id
  decode := id
  roundTrip_X := by intro x; rfl

def natIdFlowCompatible :
    natIdLens.FlowCompatible natAddSystem natAddSystem where
  encode_flow := by
    intro n x
    rfl

example {x y : Nat} (hxy : natAddSystem.reaches x y) :
    natAddSystem.reaches (natIdLens.encode x) (natIdLens.encode y) :=
  DynamicsComputationLens.reaches_encode (L := natIdLens) natIdFlowCompatible hxy

example {x : Nat} (hx : x ∈ natAddSystem.equilibriumSet) :
    natIdLens.encode x ∈ natAddSystem.equilibriumSet :=
  DynamicsComputationLens.equilibrium_encode (L := natIdLens) natIdFlowCompatible hx

example (U : Set Nat) :
    natIdLens.push (natAddSystem.reachabilityClosure U) ⊆
      natAddSystem.reachabilityClosure (natIdLens.push U) :=
  DynamicsComputationLens.push_reachabilityClosure_subset
    (L := natIdLens) natIdFlowCompatible U

example :
    natIdLens.push natAddSystem.equilibriumSet ⊆ natAddSystem.equilibriumSet :=
  DynamicsComputationLens.push_equilibrium_subset (L := natIdLens) natIdFlowCompatible

end HeytingLean.Tests.OTM.DynamicsComputation
