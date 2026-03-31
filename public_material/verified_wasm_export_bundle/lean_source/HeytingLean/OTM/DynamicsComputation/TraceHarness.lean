import HeytingLean.OTM.DynamicsComputation.IntegrationExamples

namespace HeytingLean
namespace OTM
namespace DynamicsComputation
namespace TraceHarness

open IntegrationExamples

/-- Fuel-bounded trace of TM configurations via direct `stepN`. -/
def tmTrace (TM : HeytingLean.MirandaDynamics.Computation.HaltSys Nat) (init fuel : Nat) : List Nat :=
  (List.range (fuel + 1)).map (fun k => TM.stepN k init)

/--
Fuel-bounded trace produced by iterating the evaluator code in encoded space and decoding each step.
-/
noncomputable def evaluatorDecodedTrace (code : natEndoUniversalEvaluator.Code) (init fuel : Nat) : List Nat :=
  (List.range (fuel + 1)).map (fun k =>
    natTMEncoding.decode
      (Nat.iterate (natEndoUniversalEvaluator.eval code) k (natTMEncoding.encode init)))

theorem evaluatorDecodedTrace_eq_tmTrace_counter (fuel init : Nat) :
    evaluatorDecodedTrace counterStepCode init fuel = tmTrace counterTM init fuel := by
  unfold evaluatorDecodedTrace tmTrace
  refine List.map_congr_left ?_
  intro k hk
  simpa using counter_step_code_simulates k init

theorem evaluatorDecodedTrace_counter_at_two :
    evaluatorDecodedTrace counterStepCode 0 2 = [0, 1, 2] := by
  have htrace : tmTrace counterTM 0 2 = [0, 1, 2] := by
    decide
  calc
    evaluatorDecodedTrace counterStepCode 0 2
        = tmTrace counterTM 0 2 := evaluatorDecodedTrace_eq_tmTrace_counter 2 0
    _ = [0, 1, 2] := htrace

end TraceHarness
end DynamicsComputation
end OTM
end HeytingLean
