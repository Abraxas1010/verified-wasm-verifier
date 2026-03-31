import HeytingLean.Numbers.Surreal.NoneistKripke

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal.NoneistKripke
open HeytingLean.Noneism
open HeytingLean.Noneism.KripkeProp

#check World
#check model

private def w0 : World := { stage := 0, mode := .possible }
private def w1 : World := { stage := 2, mode := .possible }

example : KripkeProp.Forces (model .constant) w0 (.eExists (.var 7)) := by
  exact forces_exists_constant w0 7

example : KripkeProp.Forces (model .varying) w1 (.eExists (.var 2)) := by
  simp [forces_exists_varying_iff, w1]

example : ¬ KripkeProp.Forces (model .varying) w0 (.eExists (.var 1)) := by
  simp [forces_exists_varying_iff, w0]

example (h : w0 ≤ w1) :
    KripkeProp.Forces (model .varying) w0 (.eExists (.var 0)) →
      KripkeProp.Forces (model .varying) w1 (.eExists (.var 0)) := by
  exact forces_exists_varying_monotone h 0

example : KripkeProp.Forces (model .constant) w0 (.pred .modePossible []) := by
  simp [forces_mode_possible_iff, w0]

example : KripkeProp.Forces (model .varying) w0 (.pred .modePossible []) ∨
    KripkeProp.Forces (model .varying) w0 (.pred .modeImpossible []) := by
  exact forces_mode_possible_or_impossible .varying w0

example :
    ¬ (KripkeProp.Forces (model .constant) w0 (.pred .modePossible []) ∧
        KripkeProp.Forces (model .constant) w0 (.pred .modeImpossible [])) := by
  exact forces_mode_not_both .constant w0

private def wImpossible : World := { stage := 1, mode := .impossible }

example : ¬ w0 ≤ wImpossible := by
  apply not_le_of_mode_mismatch
  simp [w0, wImpossible]

end Numbers
end Tests
end HeytingLean
