import HeytingLean.Numbers.Surreal.Experimental.NoneistLoss

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Experimental

private def pred0 : AttentionToken :=
  { core := PreGame.build [nullCut] [], velocity := 2, anchor := none }

example :
    boundaryLoss ⟨.actual, 0⟩ pred0 ≤ boundaryLoss ⟨.counterfactual, 0⟩ pred0 :=
  boundaryLoss_actual_le_counterfactual 0 pred0

example :
    boundaryLoss ⟨.actual, 0⟩ pred0 < boundaryLoss ⟨.counterfactual, 0⟩ pred0 := by
  apply counterfactual_loss_strict_of_positive_velocity
  decide

example :
    paradoxPairLoss 0 pred0 =
      birthError pred0.core.birth 0 + birthError pred0.core.birth 0 + pred0.velocity :=
  paradoxPairLoss_closed_form 0 pred0

example :
    boundaryLoss ⟨.actual, 0⟩ pred0 ≤ paradoxPairLoss 0 pred0 :=
  paradoxPairLoss_ge_actual 0 pred0

end Numbers
end Tests
end HeytingLean
