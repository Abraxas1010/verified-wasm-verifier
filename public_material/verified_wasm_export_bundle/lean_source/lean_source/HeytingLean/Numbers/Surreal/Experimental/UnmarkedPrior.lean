import HeytingLean.Numbers.Surreal.Experimental.NoneistAttentionBoundary

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

open HeytingLean.Numbers.SurrealCore

noncomputable section

/-- Unmarked prior token for experimental Noneist transformer initialization. -/
def unmarkedSpace : AttentionToken :=
  { core := SurrealCore.nullCut
    velocity := 0
    anchor := none }

/-- One marking step from an existing token. -/
def markFromUnmarked (t : AttentionToken) : AttentionToken :=
  { t with
    core := PreGame.build [t.core] []
    velocity := t.velocity.succ }

/-- Initialize token stream from pregames using the unmarked prior anchor policy. -/
def initWithUnmarked (xs : List PreGame) : List AttentionToken :=
  xs.map (fun g =>
    { core := g
      velocity := 0
      anchor := unmarkedSpace.anchor })

@[simp] theorem unmarked_birth_zero : unmarkedSpace.core.birth = 0 := rfl

@[simp] theorem initWithUnmarked_length_preserved (xs : List PreGame) :
    (initWithUnmarked xs).length = xs.length := by
  simp [initWithUnmarked]

/-- Marking does not decrease birthday. -/
theorem markFromUnmarked_increases_or_preserves_birth (t : AttentionToken) :
    t.core.birth ≤ (markFromUnmarked t).core.birth := by
  simp [markFromUnmarked, PreGame.build, PreGame.maxBirth]

/-- If a marked-unmarked query synchronizes, the budget is strictly positive. -/
theorem initiation_requires_positive_budget {budget : Nat} {tok : AttentionToken}
    (h : syncBudget budget (markFromUnmarked unmarkedSpace) tok = true) :
    0 < budget := by
  have hLeAnd :
      (markFromUnmarked unmarkedSpace).velocity ≤ budget ∧ tok.velocity ≤ budget := by
    simpa [syncBudget] using h
  have hLe : (markFromUnmarked unmarkedSpace).velocity ≤ budget := hLeAnd.1
  have hOne : 1 ≤ budget := by
    simpa [markFromUnmarked, unmarkedSpace] using hLe
  exact Nat.succ_le_iff.mp hOne

/-- Attention from unmarked prior is classified: unchanged or explicit boundary output. -/
theorem attention_on_unmarked_is_identity_or_boundary
    (budget : Nat) (tok : AttentionToken) :
    boundaryProjection budget unmarkedSpace tok = unmarkedSpace ∨
      (boundaryProjection budget unmarkedSpace tok).core =
        attendBoundary unmarkedSpace tok := by
  by_cases h : syncBudget budget unmarkedSpace tok
  · left
    simp [boundaryProjection, h]
  · right
    simp [boundaryProjection, h]

end

end Experimental
end Surreal
end Numbers
end HeytingLean
