import HeytingLean.Numbers.Surreal.NoneistFoundationPreservation

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal

example : isNullCut nullCut = true := by
  simp

example : isNullCut (PreGame.build [] []) = false := by
  simp [isNullCut, PreGame.build, PreGame.maxBirth]

example (x : PreGame) : mul nullCut x = nullCut := by
  exact mul_nullCut_left x

example (x : PreGame) : mul x nullCut = nullCut := by
  exact mul_nullCut_right x

example (x : PreGame) : PreGame.toIGame (mul nullCut x) = 0 := by
  exact PreGame.toIGame_mul_nullCut_left x

example (x : PreGame) : PreGame.toIGame (mul x nullCut) = 0 := by
  exact PreGame.toIGame_mul_nullCut_right x

example (x y : PreGame) :
    PreGame.toIGame (mul x y) = PreGame.toIGame x * PreGame.toIGame y := by
  exact PreGame.toIGame_mul x y

example (x y z : PreGame) :
    PreGame.toIGame (mul x (add y z)) ≈
      PreGame.toIGame (add (mul x y) (mul x z)) := by
  exact PreGame.toIGame_mul_add_equiv x y z

example (x y z : PreGame) :
    PreGame.toIGame (mul (add x y) z) ≈
      PreGame.toIGame (add (mul x z) (mul y z)) := by
  exact PreGame.toIGame_add_mul_equiv x y z

example (x y z : PreGame) :
    PreGame.toIGame (mul (mul x y) z) ≈
      PreGame.toIGame (mul x (mul y z)) := by
  exact PreGame.toIGame_mul_assoc_equiv x y z

example (x y : PreGame) :
    PreGame.toIGame (mul x y) = PreGame.toIGame (mul y x) := by
  exact PreGame.toIGame_mul_comm x y

noncomputable def anchoredNull : AnchoredPreGame :=
  withMarked nullCut markAnchor markAnchor_is_marked

example (x : AnchoredPreGame) :
    PreGame.toIGame (forget (anchoredMul anchoredNull x)) = 0 := by
  apply forget_toIGame_mul_nullCut_left
  rfl

example (x : AnchoredPreGame) :
    PreGame.toIGame (forget (anchoredMul x anchoredNull)) = 0 := by
  apply forget_toIGame_mul_nullCut_right
  rfl

example (x y : PreGame) :
    PreGame.toIGame (mul nullCut (add x y)) =
      PreGame.toIGame (add (mul nullCut x) (mul nullCut y)) := by
  exact PreGame.toIGame_mul_add_nullCut_left x y

example (x y : PreGame) :
    PreGame.toIGame (mul (add x y) nullCut) =
      PreGame.toIGame (add (mul x nullCut) (mul y nullCut)) := by
  exact PreGame.toIGame_mul_add_nullCut_right x y

example (x y : AnchoredPreGame) :
    PreGame.toIGame (forget (anchoredMul anchoredNull (anchoredAdd x y))) =
      PreGame.toIGame (forget (anchoredAdd (anchoredMul anchoredNull x) (anchoredMul anchoredNull y))) := by
  exact forget_toIGame_mul_add_nullCut_left anchoredNull x y rfl

example (x y : AnchoredPreGame) :
    PreGame.toIGame (forget (anchoredMul (anchoredAdd x y) anchoredNull)) =
      PreGame.toIGame (forget (anchoredAdd (anchoredMul x anchoredNull) (anchoredMul y anchoredNull))) := by
  exact forget_toIGame_mul_add_nullCut_right x y anchoredNull rfl

example (x y : AnchoredPreGame) :
    PreGame.toIGame (forget (anchoredMul x y)) =
      PreGame.toIGame (forget (anchoredMul y x)) := by
  exact forget_toIGame_mul_comm x y

end Numbers
end Tests
end HeytingLean
