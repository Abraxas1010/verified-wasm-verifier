import Lean
import Lean.Elab.Tactic
import HeytingLean.ProofState.Snapshot

open Lean Elab Tactic Meta

namespace HeytingLean
namespace ProofState

elab "emit_typed_goals" : tactic => do
  let goals ← Lean.Elab.Tactic.getUnsolvedGoals
  let snapshot ← snapshotGoals goals
  Lean.logInfo m!"[PROOF_STATE_JSON]{(toJson snapshot).compress}[/PROOF_STATE_JSON]"
  for goal in goals do
    Lean.Elab.admitGoal goal

end ProofState
end HeytingLean
