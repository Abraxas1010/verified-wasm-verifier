import HeytingLean.Numbers.Surreal.Experimental.UnmarkedPrior
import HeytingLean.Numbers.Surreal.Experimental.NoneistTransformerToy

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Experimental

private def tok0 : AttentionToken :=
  { core := nullCut, velocity := 0, anchor := none }

example : unmarkedSpace.core.birth = 0 := by
  exact unmarked_birth_zero

example : (initWithUnmarked [nullCut, nullCut]).length = 2 := by
  simp

example : tok0.core.birth ≤ (markFromUnmarked tok0).core.birth :=
  markFromUnmarked_increases_or_preserves_birth tok0

example :
    0 < 2 := by
  have hSync : syncBudget 2 (markFromUnmarked unmarkedSpace) tok0 = true := by
    simp [syncBudget, markFromUnmarked, unmarkedSpace, tok0]
  exact initiation_requires_positive_budget hSync

example :
    boundaryProjection 0 unmarkedSpace tok0 = unmarkedSpace ∨
      (boundaryProjection 0 unmarkedSpace tok0).core =
        attendBoundary unmarkedSpace tok0 :=
  attention_on_unmarked_is_identity_or_boundary 0 tok0

example :
    (runFromPregames ⟨2⟩ [nullCut, nullCut]).length = 2 := by
  simp [runFromPregames]

end Numbers
end Tests
end HeytingLean
