/-!
# ATP.DifferentiableATP.RewardSignal

Shared reward primitives for differentiable ATP search/training.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

/--
Hierarchical subgoal reward with optional composition bonus:

- partial credit: `subgoalsSolved / totalSubgoals`
- composition bonus: `compositionBonus` when all subgoals are solved
-/
def hierarchicalSubgoalReward
    (subgoalsSolved totalSubgoals : Nat)
    (compositionBonus : Rat := (1 : Rat) / 2) : Rat :=
  if totalSubgoals = 0 then
    0
  else
    let solved := min subgoalsSolved totalSubgoals
    let solvedFrac := (Int.ofNat solved : Rat) / (Int.ofNat totalSubgoals : Rat)
    let completeBonus := if solved = totalSubgoals then compositionBonus else 0
    solvedFrac + completeBonus

end DifferentiableATP
end ATP
end HeytingLean
