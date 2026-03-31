import HeytingLean.Numbers.Surreal.Experimental.NoneistAttentionCore
import HeytingLean.Numbers.Surreal.Experimental.NoneistAttentionBoundary

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Experimental

private def t0 : AttentionToken :=
  { core := nullCut, velocity := 0, anchor := none }

private def tFast : AttentionToken :=
  { core := PreGame.build [nullCut] [], velocity := 5, anchor := none }

example : syncBudget 1 t0 t0 = true := by
  simp [syncBudget, t0]

example : syncBudget 1 tFast t0 = false := by
  simp [syncBudget, tFast, t0]

example : (attentionStep 1 tFast t0 t0).core = attendBoundary tFast t0 := by
  apply attentionStep_unobtainable_returns_boundary
  simp [syncBudget, tFast, t0]

example :
    t0.core.birth ≤ (attentionStep 2 t0 t0 t0).core.birth := by
  apply attentionStep_obtainable_preserves_birth_upper_bound
  simp [syncBudget, t0]

example :
    transformerLayerStable 3 [t0, tFast] :=
  transformerLayer_stable 3 [t0, tFast]

example :
    (boundaryProjection 1 tFast t0).core = attendBoundary tFast t0 := by
  apply boundaryProjection_unsync_core
  simp [syncBudget, tFast, t0]

end Numbers
end Tests
end HeytingLean
