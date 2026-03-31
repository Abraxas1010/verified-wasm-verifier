import HeytingLean.OTM.DynamicsComputation.ForwardCorrespondence
import HeytingLean.OTM.DynamicsComputation.ReverseCorrespondence
import HeytingLean.OTM.DynamicsComputation.RealizabilityBridge
import HeytingLean.OTM.DynamicsComputation.Instances.BilliardsBridge
import HeytingLean.OTM.DynamicsComputation.Instances.EulerBridge
import HeytingLean.OTM.DynamicsComputation.Instances.NavierStokesBridge
import HeytingLean.OTM.DynamicsComputation.Lens.DynamicsComputationLens
import HeytingLean.OTM.DynamicsComputation.IntegrationExamples

namespace HeytingLean
namespace OTM
namespace DynamicsComputation

open HeytingLean.MirandaDynamics.Computation

universe u v

/--
First conditional packaging theorem for the dynamics-computation program:
- forward direction contributes a concrete nucleus witness from the TM lane,
- reverse direction contributes evaluator universality (under explicit assumptions).
-/
theorem first_correspondence_milestone
    {Cfg : Type u} [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (init : Cfg)
    (E : UniversalClosedEvaluator Cfg) :
    (∃ J : Nucleus (Set Cfg), ∀ U : Set Cfg, J U = U) ∧
    (∃ otm : Machine Unit (Set Cfg),
      otm_decode_cfg (Cfg := Cfg) otm.runtime.control = init ∧
      ∀ fuel,
        otm_decode_cfg (Cfg := Cfg) ((Machine.run fuel otm).runtime.control) = TM.stepN fuel init) ∧
    (∀ f : Set Cfg → Set Cfg, ∃ c : E.Code, E.eval c = f) := by
  refine ⟨?_, ?_, ?_⟩
  · exact tm_complete_implies_has_nucleus (Cfg := Cfg)
  · exact forward_trace_correspondence (Cfg := Cfg) TM init
  · intro f
    exact E.universal f

/--
Operationally strengthened correspondence bundle:
- forward nucleus + OTM trace correspondence,
- reverse evaluator-driven TM simulation (under encoding assumptions),
- discrete undecidability transfer witness.
-/
theorem correspondence_operational_bundle
    {Cfg : Type u} [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (init : Cfg)
    (E : UniversalClosedEvaluator Cfg)
    (Enc : TMEncoding Cfg Cfg)
    (n : Nat) :
    (∃ J : Nucleus (Set Cfg), ∀ U : Set Cfg, J U = U) ∧
    (∃ otm : Machine Unit (Set Cfg),
      otm_decode_cfg (Cfg := Cfg) otm.runtime.control = init ∧
      ∀ fuel,
        otm_decode_cfg (Cfg := Cfg) ((Machine.run fuel otm).runtime.control) = TM.stepN fuel init) ∧
    (∃ code : E.Code,
      ∀ fuel cfg,
        Enc.decode (Nat.iterate (E.eval code) fuel (Enc.encode cfg)) = TM.stepN fuel cfg) ∧
    (¬ComputablePred (fun c : Nat.Partrec.Code => HeytingLean.MirandaDynamics.Discrete.ReachesPeriod2 n c)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tm_complete_implies_has_nucleus (Cfg := Cfg)
  · exact forward_trace_correspondence (Cfg := Cfg) TM init
  · exact nucleus_universal_implies_tm_simulation
      (X := Cfg) (Cfg := Cfg) (tm_id_nucleus (Cfg := Cfg)) E Enc TM
  · exact periodic_orbit_predicate_not_computable n

/--
Concrete specialization of the strengthened bundle to the existing `counterTM` lane.
-/
theorem correspondence_operational_bundle_counter :
    (∃ J : Nucleus (Set Nat), ∀ U : Set Nat, J U = U) ∧
    (∃ otm : Machine Unit (Set Nat),
      otm_decode_cfg (Cfg := Nat) otm.runtime.control = 0 ∧
      ∀ fuel,
        otm_decode_cfg (Cfg := Nat) ((Machine.run fuel otm).runtime.control) = counterTM.stepN fuel 0) ∧
    (∃ code : IntegrationExamples.natEndoUniversalEvaluator.Code,
      ∀ fuel cfg,
        IntegrationExamples.natTMEncoding.decode
          (Nat.iterate (IntegrationExamples.natEndoUniversalEvaluator.eval code) fuel
            (IntegrationExamples.natTMEncoding.encode cfg)) =
          counterTM.stepN fuel cfg) ∧
    (¬ComputablePred (fun c : Nat.Partrec.Code => HeytingLean.MirandaDynamics.Discrete.ReachesPeriod2 1 c)) := by
  exact correspondence_operational_bundle
    (Cfg := Nat)
    counterTM
    0
    IntegrationExamples.natEndoUniversalEvaluator
    IntegrationExamples.natTMEncoding
    1

end DynamicsComputation
end OTM
end HeytingLean
