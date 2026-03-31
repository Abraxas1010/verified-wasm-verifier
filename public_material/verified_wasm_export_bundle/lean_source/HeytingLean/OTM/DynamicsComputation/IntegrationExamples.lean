import HeytingLean.OTM.DynamicsComputation.ReverseCorrespondence
import HeytingLean.OTM.PerspectivalHalting
import HeytingLean.OTM.TuringSubsumption

namespace HeytingLean
namespace OTM
namespace DynamicsComputation
namespace IntegrationExamples

/--
A concrete universal evaluator on `Set Nat` endomaps:
codes are endomaps themselves and evaluation is identity.
-/
noncomputable def natEndoUniversalEvaluator : UniversalClosedEvaluator Nat where
  Code := Set Nat → Set Nat
  eval := fun f => f
  universal := by
    intro f
    exact ⟨f, rfl⟩

/-- Concrete encoding used in reverse-direction integration examples. -/
noncomputable def natTMEncoding : TMEncoding Nat Nat where
  encode := otm_encode_cfg (Cfg := Nat)
  decode := otm_decode_cfg (Cfg := Nat)
  decode_encode := by
    intro n
    simpa using otm_decode_cfg_encode (Cfg := Nat) n

/-- Identity nucleus on `Set Nat`, reused as the ambient closed-proposition modality. -/
noncomputable def natIdNucleus : Nucleus (Set Nat) :=
  tm_id_nucleus (Cfg := Nat)

/-- Counter-TM step code in the concrete evaluator. -/
noncomputable def counterStepCode : natEndoUniversalEvaluator.Code :=
  fun s => natTMEncoding.encode (counterTM.step (natTMEncoding.decode s))

@[simp] theorem eval_counterStepCode :
    natEndoUniversalEvaluator.eval counterStepCode =
      (fun s => natTMEncoding.encode (counterTM.step (natTMEncoding.decode s))) := rfl

/--
Fuel-bounded reverse simulation for the explicit counter-TM code.
-/
theorem counter_step_code_simulates :
    ∀ fuel init,
      natTMEncoding.decode
          (Nat.iterate (natEndoUniversalEvaluator.eval counterStepCode) fuel
            (natTMEncoding.encode init)) = counterTM.stepN fuel init :=
  decode_iter_step_code_eq_stepN
    (X := Nat) (Cfg := Nat)
    natEndoUniversalEvaluator
    natTMEncoding
    counterTM
    (code := counterStepCode)
    eval_counterStepCode

/--
Reverse correspondence witness specialized to the counter-TM lane.
-/
theorem counter_tm_reverse_witness :
    ∃ code : natEndoUniversalEvaluator.Code,
      ∀ fuel init,
        natTMEncoding.decode
            (Nat.iterate (natEndoUniversalEvaluator.eval code) fuel
              (natTMEncoding.encode init)) = counterTM.stepN fuel init :=
  nucleus_universal_implies_tm_simulation
    (X := Nat) (Cfg := Nat)
    natIdNucleus
    natEndoUniversalEvaluator
    natTMEncoding
    counterTM

/-- Concrete sanity theorem at the known halting witness fuel. -/
theorem counter_step_code_at_two :
    natTMEncoding.decode
        (Nat.iterate (natEndoUniversalEvaluator.eval counterStepCode) 2
          (natTMEncoding.encode 0)) = 2 := by
  have hsim := counter_step_code_simulates 2 0
  simpa [counterTM_stepN_eq_add] using hsim

end IntegrationExamples
end DynamicsComputation
end OTM
end HeytingLean
