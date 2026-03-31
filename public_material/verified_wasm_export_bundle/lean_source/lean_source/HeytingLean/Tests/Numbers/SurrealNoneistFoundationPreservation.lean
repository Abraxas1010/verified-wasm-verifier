import HeytingLean.Numbers.Surreal.NoneistFoundationPreservation

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

example :
    PreGame.toIGame (forget (anchoredAdd genesis counterGenesis)) =
      PreGame.toIGame (forget genesis) + PreGame.toIGame (forget counterGenesis) := by
  simpa using forget_toIGame_add genesis counterGenesis

example :
    PreGame.toIGame (forget (anchoredAdd genesis counterGenesis)) =
      PreGame.toIGame (forget (anchoredAdd counterGenesis genesis)) := by
  simpa using forget_toIGame_add_comm genesis counterGenesis

example :
    PreGame.toIGame (forget (anchoredAdd (anchoredAdd genesis counterGenesis) genesis)) =
      PreGame.toIGame (forget (anchoredAdd genesis (anchoredAdd counterGenesis genesis))) := by
  simpa using forget_toIGame_add_assoc genesis counterGenesis genesis

example :
    PreGame.toIGame (forget (anchoredAdd (anchoredNeg genesis) genesis)) ≈ 0 := by
  simpa using forget_toIGame_add_left_neg_equiv_zero genesis

example :
    PreGame.toIGame (forget (anchoredAdd genesis (anchoredNeg genesis))) ≈ 0 := by
  simpa using forget_toIGame_add_right_neg_equiv_zero genesis

example :
    PreGame.toIGame (forget (anchoredAdd (anchoredNeg genesis) (anchoredAdd genesis counterGenesis)))
      ≈ PreGame.toIGame (forget counterGenesis) := by
  simpa using forget_toIGame_add_left_cancel_equiv genesis counterGenesis

example :
    PreGame.toIGame (forget (anchoredAdd genesis (anchoredAdd (anchoredNeg genesis) counterGenesis)))
      ≈ PreGame.toIGame (forget counterGenesis) := by
  simpa using forget_toIGame_add_right_cancel_equiv genesis counterGenesis

example :
    PreGame.toIGame (forget (anchoredMul genesis counterGenesis)) =
      PreGame.toIGame (forget genesis) * PreGame.toIGame (forget counterGenesis) := by
  simpa using forget_toIGame_mul genesis counterGenesis

example :
    PreGame.toIGame (forget (anchoredMul genesis (anchoredAdd counterGenesis genesis))) ≈
      PreGame.toIGame
        (forget (anchoredAdd (anchoredMul genesis counterGenesis) (anchoredMul genesis genesis))) := by
  simpa using forget_toIGame_mul_add_equiv genesis counterGenesis genesis

example :
    PreGame.toIGame (forget (anchoredMul (anchoredAdd genesis counterGenesis) genesis)) ≈
      PreGame.toIGame
        (forget (anchoredAdd (anchoredMul genesis genesis) (anchoredMul counterGenesis genesis))) := by
  simpa using forget_toIGame_add_mul_equiv genesis counterGenesis genesis

example :
    PreGame.toIGame (forget (anchoredMul (anchoredMul genesis counterGenesis) genesis)) ≈
      PreGame.toIGame (forget (anchoredMul genesis (anchoredMul counterGenesis genesis))) := by
  simpa using forget_toIGame_mul_assoc_equiv genesis counterGenesis genesis

end Numbers
end Tests
end HeytingLean
