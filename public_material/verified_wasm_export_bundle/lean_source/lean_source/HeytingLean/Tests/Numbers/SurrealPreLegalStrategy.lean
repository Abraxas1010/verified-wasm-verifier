import HeytingLean.Numbers.Surreal.PreLegalGame
import HeytingLean.Numbers.Surreal.StrategyOrder
import HeytingLean.Numbers.Surreal.DialecticaBridge
import HeytingLean.Numbers.Surreal.Tactics

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal

#check PreLegalGame
#check StrategyOrder.sum
#check DialecticaBridge.toProgram

def preLegalEmpty : PreLegalGame :=
  { L := [], R := [] }

def preLegalSingletonLeft : PreLegalGame :=
  { L := [HeytingLean.Numbers.SurrealCore.nullCut], R := [] }

def preLegalContradictory : PreLegalGame :=
  { L := [HeytingLean.Numbers.SurrealCore.nullCut]
    R := [HeytingLean.Numbers.SurrealCore.nullCut] }

example :
    PreLegalGame.legalCut ({ L := [], R := [] } : PreLegalGame) := by
  exact PreLegalGame.legalCut_empty

example :
    ¬ PreLegalGame.contradictory ({ L := [], R := [] } : PreLegalGame) := by
  exact PreLegalGame.not_contradictory_empty

example (x : StrategyOrder.Game) : StrategyOrder.sum StrategyOrder.zero x = x := by
  exact StrategyOrder.sum_zero_left x

example (x : StrategyOrder.Game) : StrategyOrder.sum x StrategyOrder.zero = x := by
  exact StrategyOrder.sum_zero_right x

example (x y z : StrategyOrder.Game) :
    StrategyOrder.sum (StrategyOrder.sum x y) z =
      StrategyOrder.sum x (StrategyOrder.sum y z) := by
  exact StrategyOrder.sum_assoc x y z

example (x : PreLegalGame) :
    (DialecticaBridge.toProgram x).root < (DialecticaBridge.toProgram x).ops.size := by
  exact DialecticaBridge.toProgram_root_lt_size x

example :
    (DialecticaBridge.toProgram preLegalEmpty).ops.size = 1 := by
  native_decide

example :
    (DialecticaBridge.toProgram preLegalSingletonLeft).ops.size = 2 := by
  native_decide

example :
    (DialecticaBridge.toProgram preLegalSingletonLeft).root = 1 := by
  native_decide

example :
    DialecticaBridge.toProgram preLegalEmpty ≠ DialecticaBridge.toProgram preLegalSingletonLeft := by
  native_decide

example :
    PreLegalGame.crossLegal ({ L := [], R := [] } : PreLegalGame) preLegalSingletonLeft := by
  exact PreLegalGame.crossLegal_empty_left preLegalSingletonLeft

example :
    PreLegalGame.legalCut (StrategyOrder.sum ({ L := [], R := [] } : PreLegalGame) preLegalSingletonLeft) := by
  apply StrategyOrder.legalCut_sum_of_cross
  · exact PreLegalGame.legalCut_empty
  · intro l hl r hr
    simp [preLegalSingletonLeft] at hr
  · exact PreLegalGame.crossLegal_empty_left preLegalSingletonLeft

example : PreLegalGame.contradictory preLegalContradictory := by
  refine ⟨HeytingLean.Numbers.SurrealCore.nullCut, ?_, HeytingLean.Numbers.SurrealCore.nullCut, ?_, ?_⟩
  · simp [preLegalContradictory]
  · simp [preLegalContradictory]
  · simp [HeytingLean.Numbers.SurrealCore.lt, HeytingLean.Numbers.SurrealCore.le,
      HeytingLean.Numbers.SurrealCore.leAt, HeytingLean.Numbers.SurrealCore.nullCut]

example :
    PreLegalGame.contradictory (StrategyOrder.sum preLegalContradictory preLegalEmpty) := by
  exact StrategyOrder.contradictory_sum_left preLegalContradictory preLegalEmpty
    (by
      refine ⟨HeytingLean.Numbers.SurrealCore.nullCut, ?_, HeytingLean.Numbers.SurrealCore.nullCut, ?_, ?_⟩
      · simp [preLegalContradictory]
      · simp [preLegalContradictory]
      · simp [HeytingLean.Numbers.SurrealCore.lt, HeytingLean.Numbers.SurrealCore.le,
          HeytingLean.Numbers.SurrealCore.leAt, HeytingLean.Numbers.SurrealCore.nullCut])

example (A : Set HeytingLean.Numbers.SurrealCore.PreGame) :
    setBoundaryOps.nonExistent A := by
  noneist_simp

end Numbers
end Tests
end HeytingLean
