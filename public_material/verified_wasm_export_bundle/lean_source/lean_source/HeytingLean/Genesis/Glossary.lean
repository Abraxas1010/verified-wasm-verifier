import HeytingLean.Genesis.CoGame
import HeytingLean.Genesis.Iterant
import HeytingLean.Genesis.Life
import HeytingLean.Genesis.Void

/-!
# Genesis.Glossary

Glossary anchors for Genesis Phase 1.
-/

namespace HeytingLean.Genesis

/-- Witness: the canonical self-referential co-game. -/
abbrev Witness : CoGame := CoGame.Life

/-- Void: canonical empty-option co-game. -/
abbrev PrimalVoid : CoGame := CoGame.Void

/-- Cantor-cut proxy for Phase 1: infinite binary path space. -/
abbrev CantorCut : Type := Nat → Bool

/-- Oscillation carrier used by witness phases. -/
abbrev Oscillation := Iterant Bool

/-- Stabilization depth anchor: depth-indexed approximation parameter. -/
abbrev StabilizationDepth := Nat

/-- Observer v1 shape for Phase 1 planning. -/
structure ObserverV1 where
  depth : Nat
  choices : Fin depth → Bool
  phase : Iterant Bool

/-- Completed observer trajectories (Phase 2 anchor). -/
abbrev CompletedObserver : Type := Nat → Bool

end HeytingLean.Genesis
