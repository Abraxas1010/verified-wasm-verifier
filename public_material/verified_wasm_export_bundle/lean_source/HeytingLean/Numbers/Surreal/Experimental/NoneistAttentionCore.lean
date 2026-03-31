import HeytingLean.Numbers.Surreal.NoneistFoundation

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

open HeytingLean.Numbers.SurrealCore

noncomputable section

/-- Experimental token carrier for Noneist attention prototypes. -/
structure AttentionToken where
  core : PreGame
  velocity : Nat := 0
  anchor : Option Surreal.NObj := none

/-- Max birthday across a token list. -/
def maxBirthTokens : List AttentionToken -> Nat
  | [] => 0
  | t :: ts => Nat.max t.core.birth (maxBirthTokens ts)

/-- Membership implies birthday bounded by `maxBirthTokens`. -/
theorem le_maxBirthTokens_of_mem {x : AttentionToken} {xs : List AttentionToken}
    (h : x ∈ xs) :
    x.core.birth ≤ maxBirthTokens xs := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
      simp at h
      simp [maxBirthTokens]
      rcases h with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

/-- Velocity-gated synchronizability check. -/
def syncBudget (budget : Nat) (q k : AttentionToken) : Bool :=
  decide (q.velocity ≤ budget) && decide (k.velocity ≤ budget)

/-- Self-sync succeeds when the token velocity fits budget. -/
theorem syncBudget_self {budget : Nat} {t : AttentionToken}
    (h : t.velocity ≤ budget) :
    syncBudget budget t t = true := by
  simp [syncBudget, h]

/-- Boundary projection between query and key. -/
def attendBoundary (q k : AttentionToken) : PreGame :=
  PreGame.build [q.core] [k.core]

/-- One experimental attention update step. -/
def attentionStep (budget : Nat)
    (q k v : AttentionToken) : AttentionToken :=
  if syncBudget budget q k then
    { core := PreGame.build [q.core] [k.core, v.core]
      velocity := Nat.max q.velocity (Nat.max k.velocity v.velocity)
      anchor := q.anchor <|> k.anchor <|> v.anchor }
  else
    { core := attendBoundary q k
      velocity := Nat.max q.velocity k.velocity
      anchor := q.anchor <|> k.anchor }

/-- Unsynchronized step returns explicit boundary core. -/
theorem attentionStep_unobtainable_returns_boundary
    {budget : Nat} {q k v : AttentionToken}
    (h : syncBudget budget q k = false) :
    (attentionStep budget q k v).core = attendBoundary q k := by
  simp [attentionStep, h]

/-- Synchronized step never decreases query birthday. -/
theorem attentionStep_obtainable_preserves_birth_upper_bound
    {budget : Nat} {q k v : AttentionToken}
    (h : syncBudget budget q k = true) :
    q.core.birth ≤ (attentionStep budget q k v).core.birth := by
  simp [attentionStep, h, PreGame.build, PreGame.maxBirth]
  have hq : q.core.birth ≤ Nat.max q.core.birth (Nat.max k.core.birth v.core.birth) :=
    Nat.le_max_left _ _
  exact Nat.le_trans hq (Nat.le_succ _)

/-- Self-attention toy layer. -/
def transformerLayer (budget : Nat) (xs : List AttentionToken) : List AttentionToken :=
  xs.map (fun x => attentionStep budget x x x)

/-- Layer-stability predicate used by tests for regression checks. -/
def transformerLayerStable (budget : Nat) (xs : List AttentionToken) : Prop :=
  ∀ y, y ∈ transformerLayer budget xs ->
    y.core.birth ≤ Nat.succ (maxBirthTokens xs)

private theorem attentionStep_self_birth (budget : Nat) (x : AttentionToken) :
    (attentionStep budget x x x).core.birth = Nat.succ x.core.birth := by
  by_cases h : syncBudget budget x x
  · simp [attentionStep, h, PreGame.build, PreGame.maxBirth]
  · simp [attentionStep, h, attendBoundary, PreGame.build, PreGame.maxBirth]

/-- The self-attention layer is birthday-bounded by one step over max input birthday. -/
theorem transformerLayer_stable (budget : Nat) (xs : List AttentionToken) :
    transformerLayerStable budget xs := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  calc
    (attentionStep budget x x x).core.birth = Nat.succ x.core.birth :=
      attentionStep_self_birth budget x
    _ ≤ Nat.succ (maxBirthTokens xs) :=
      Nat.succ_le_succ (le_maxBirthTokens_of_mem hx)

end

end Experimental
end Surreal
end Numbers
end HeytingLean
