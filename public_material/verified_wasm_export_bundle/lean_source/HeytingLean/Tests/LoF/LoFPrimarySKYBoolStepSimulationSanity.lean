import HeytingLean.LoF.Correspondence.LoFPrimarySKYBoolStepSimulation

/-!
# LoFPrimarySKYBoolStepSimulationSanity

Sanity checks for the “what can/can’t be simulated by directed SKY reduction” layer for the
LoFPrimary → SKY Church boolean bridge.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Correspondence

open LoFPrimarySKYBoolStepSimulation

namespace LoFPrimarySKYBoolStepSimulationSanity

#check LoFPrimarySKYBoolStepSimulation.calling_simulated
#check LoFPrimarySKYBoolStepSimulation.void_left_simulated

#check LoFPrimarySKYBoolStepSimulation.step_boolObsEq_toSKYBool
#check LoFPrimarySKYBoolStepSimulation.steps_boolObsEq_toSKYBool

#check LoFPrimarySKYBoolStepSimulation.trueAlt_obsEq_tt
#check LoFPrimarySKYBoolStepSimulation.trueAlt_not_steps_tt

end LoFPrimarySKYBoolStepSimulationSanity

end LoF
end Tests
end HeytingLean
