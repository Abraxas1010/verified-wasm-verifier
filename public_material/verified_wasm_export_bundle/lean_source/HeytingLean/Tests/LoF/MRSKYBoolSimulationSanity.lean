import HeytingLean.LoF.MRSystems.SKYBoolSimulation

/-!
Sanity checks for `LoF/MRSystems/SKYBoolSimulation.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.MRSystems

namespace MRSKYBoolSimulationSanity

open BoolSim

#check BoolSim.toSKYFun1
#check BoolSim.toSKYFun2

#check BoolSim.steps_apply_toSKYFun1
#check BoolSim.steps_apply_toSKYFun2

#check BoolSim.steps_applyWordTerm_correct

end MRSKYBoolSimulationSanity

end LoF
end Tests
end HeytingLean

