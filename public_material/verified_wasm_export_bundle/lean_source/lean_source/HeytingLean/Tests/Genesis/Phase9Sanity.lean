import HeytingLean.Genesis

/-!
# Genesis Phase 9 Sanity

Cantor-cut transport + bounded transfinite interior checks.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open Cardinal

#check cantorCut_completedObserver_equiv
#check cantorCut_to_witnessInterior
#check cantorCut_transport_ready
#check level0_paths_cardinality
#check level1_paths_cardinality
#check level1_paths_cardinality_step

def pTrue : EvalPath := fun _ => true
def pFalse : EvalPath := fun _ => false

example : eventualStabilizes (cantorCut_to_witnessInterior pTrue 0).source := by
  exact (cantorCut_transport_ready pTrue 0).2 rfl

example : ¬ eventualStabilizes (cantorCut_to_witnessInterior pFalse 0).source := by
  intro hs
  have hhead : pFalse 0 = true := (cantorCut_transport_ready pFalse 0).1 hs
  simp [pFalse] at hhead

example : #Level1Paths = 2 ^ #Level0Paths := by
  exact level1_paths_cardinality_step

end HeytingLean.Tests.Genesis

