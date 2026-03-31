import HeytingLean.Numbers.Surreal.Experimental.NoneistAttentionCore

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

open HeytingLean.Numbers.SurrealCore

noncomputable section

/-- Keep query unchanged when synchronized; otherwise project to boundary. -/
def boundaryProjection (budget : Nat) (q k : AttentionToken) : AttentionToken :=
  if syncBudget budget q k then q
  else
    { core := attendBoundary q k
      velocity := Nat.max q.velocity k.velocity
      anchor := q.anchor <|> k.anchor }

@[simp] theorem boundaryProjection_sync
    {budget : Nat} {q k : AttentionToken}
    (h : syncBudget budget q k = true) :
    boundaryProjection budget q k = q := by
  simp [boundaryProjection, h]

@[simp] theorem boundaryProjection_unsync_core
    {budget : Nat} {q k : AttentionToken}
    (h : syncBudget budget q k = false) :
    (boundaryProjection budget q k).core = attendBoundary q k := by
  simp [boundaryProjection, h]

/-- Boundary projection never drops below query birthday. -/
theorem boundaryProjection_birth_ge_query
    (budget : Nat) (q k : AttentionToken) :
    q.core.birth ≤ (boundaryProjection budget q k).core.birth := by
  by_cases h : syncBudget budget q k
  · simp [boundaryProjection, h]
  · simp [boundaryProjection, h, attendBoundary, PreGame.build, PreGame.maxBirth]
    have hq : q.core.birth ≤ Nat.max q.core.birth k.core.birth := Nat.le_max_left _ _
    exact Nat.le_trans hq (Nat.le_succ _)

end

end Experimental
end Surreal
end Numbers
end HeytingLean
