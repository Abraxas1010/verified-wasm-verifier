import HeytingLean.Basic

/-
# Blockchain.Consensus.StatePruning

Example model for state-pruning safety: pruning away "old" blocks preserves
the portion of the history that is still needed for current and future
checks.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace StatePruning

/-- Blocks are modelled as natural numbers (heights). -/
abbrev BlockId := Nat

/-- A simple block history as a list of block identifiers. -/
structure History where
  blocks : List BlockId
  deriving Repr

/-- Prune all blocks with height strictly less than `n`, keeping only
    those at height `≥ n`. -/
def pruneFrom (h : History) (n : Nat) : History :=
  { blocks := h.blocks.filter (fun b => n ≤ b) }

/-- The set of blocks that are "needed" at or after height `n`: those
    whose height is at least `n`. -/
def neededFrom (h : History) (n : Nat) : List BlockId :=
  h.blocks.filter (fun b => n ≤ b)

/-- State-pruning safety statement: pruning from height `n` keeps
    exactly the blocks that are still needed from `n` onwards. -/
def Statement : Prop :=
  ∀ (h : History) (n : Nat),
    (pruneFrom h n).blocks = neededFrom h n

/-- `Statement` holds by unfolding `pruneFrom`/`neededFrom`. -/
theorem statement_holds : Statement := by
  intro h n
  rfl

end StatePruning
end Consensus
end Blockchain
end HeytingLean
