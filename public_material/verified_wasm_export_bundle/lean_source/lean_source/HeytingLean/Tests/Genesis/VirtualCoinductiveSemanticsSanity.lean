import HeytingLean.Genesis

/-!
# Genesis Virtual Coinductive Semantics Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis

#check succOnFin
#check cycleCoGame
#check cyclePhaseAt
#check evalCycle2
#check evalCycle2_equiv_iterant
#check evalCycleN_has_periodic_phase
#check unroll_preserves_prefix_semantics
#check life_as_cycle_special_case

example : evalCycle2 true = evalLife true := by
  exact evalCycle2_equiv_iterant true

example : evalCycle2 false = evalLife false := by
  exact evalCycle2_equiv_iterant false

example (n k : Nat) :
    evalCycleNPhase n true (k + 2) = evalCycleNPhase n true k := by
  exact evalCycleN_has_periodic_phase n true k

example (n depth : Nat) :
    virtualInterpretUnroll depth (virtualUnroll depth (cycleCoGame n)) = nesting depth := by
  exact unroll_preserves_prefix_semantics n depth

example : CoGame.Bisim (cycleCoGame 0) CoGame.Life := life_as_cycle_special_case

end HeytingLean.Tests.Genesis
