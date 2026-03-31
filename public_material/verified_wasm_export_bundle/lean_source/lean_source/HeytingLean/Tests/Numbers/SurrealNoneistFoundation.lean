import HeytingLean.Numbers.Surreal.NoneistFoundation

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

/-! Smoke tests for Noneism-anchored Surreal construction. -/

#check AnchoredPreGame
#check genesis
#check counterGenesis

example : genesis.polarity = .mark := rfl

example : counterGenesis.polarity = .unmark := rfl

example : genesis.core.birth = 1 := by
  simp [genesis_birth]

example : genesis.core ≠ HeytingLean.Numbers.SurrealCore.nullCut := genesis_not_nullCut

example : genesis.anchor ≠ counterGenesis.anchor := genesis_anchor_ne_counterAnchor

example :
    forget (anchoredAdd genesis counterGenesis) =
      HeytingLean.Numbers.SurrealCore.add genesis.core counterGenesis.core := by
  simp [forget_add]

example :
    forget (anchoredMul genesis counterGenesis) =
      HeytingLean.Numbers.SurrealCore.mul genesis.core counterGenesis.core := by
  simp [forget_mul]

example :
    forget (anchoredNeg genesis) = HeytingLean.Numbers.SurrealCore.neg genesis.core := by
  simp [forget_neg]

example : (anchoredAdd genesis counterGenesis).anchor = genesis.anchor := by
  simp [add_anchor]

example : (anchoredMul genesis counterGenesis).polarity = genesis.polarity := by
  simp [mul_polarity]

example : (anchoredNeg genesis).anchor = stepN genesis.anchor := by
  simp [neg_anchor_step]

private theorem genesis_mark : IsMark genesis.anchor := by
  simpa [Polarity.holds, genesis_polarity] using genesis.anchor_valid

private theorem counter_unmark : IsUnmark counterGenesis.anchor := by
  simpa [Polarity.holds, counterGenesis_polarity] using counterGenesis.anchor_valid

example :
    (anchoredNeg (withMarked genesis.core genesis.anchor genesis_mark)).polarity = .unmark := by
  rfl

example :
    (anchoredNeg (withUnmarked counterGenesis.core counterGenesis.anchor counter_unmark)).polarity = .mark := by
  rfl

end Numbers
end Tests
end HeytingLean
