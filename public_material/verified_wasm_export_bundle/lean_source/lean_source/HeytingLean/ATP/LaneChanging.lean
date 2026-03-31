import HeytingLean.ATP.ProofNetwork

/-!
# ATP.LaneChanging

Lane-changing ATP scaffolding.

This module does **not** attempt to solve Lean goals directly. Instead it provides:
- a `ProofPosition` record (current lens + depth + history),
- a deterministic “next lens” policy,
- a step function that switches lenses when an external “stuck” oracle fires.

This is sufficient to wire “lane change” bookkeeping into the proof network and later replace the
oracle with real proof-search signals.
-/

namespace HeytingLean
namespace ATP

open HeytingLean.Embeddings

/-- Deterministic lens rotation used by the scaffold. -/
def nextLens : LensID → LensID
  | .omega => .tensor
  | .tensor => .graph
  | .graph => .clifford
  | .clifford => .topology
  | .topology => .matula
  | .matula => .region
  | .region => .omega

structure ProofPosition where
  lens : LensID
  depth : Nat := 0
  history : List LensID := []
  deriving Repr

inductive LaneDecision where
  | stay
  | switch (newLens : LensID)
  deriving Repr, DecidableEq

/-- One lane-changing step driven by an external “stuck” oracle. -/
def step (isStuck : LensID → Bool) (pos : ProofPosition) : ProofPosition × LaneDecision :=
  if isStuck pos.lens then
    let newLens := nextLens pos.lens
    ({ lens := newLens, depth := pos.depth + 1, history := pos.lens :: pos.history }, .switch newLens)
  else
    ({ pos with depth := pos.depth + 1, history := pos.lens :: pos.history }, .stay)

end ATP
end HeytingLean
