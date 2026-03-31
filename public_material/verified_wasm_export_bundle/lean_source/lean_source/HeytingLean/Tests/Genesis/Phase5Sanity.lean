import HeytingLean.Genesis

/-!
# Genesis Phase 5 Sanity

Hardening-only regression checks for the Phase 1-4 surfaces.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open CoGame

#check void_baseStabilizes
#check life_not_baseStabilizes
#check interior_detects_obstruction_iff
#check noneist_objects_are_unstabilizable

def wi2 : WitnessInterior := lifeInterior 2

example : baseStabilizes CoGame.Void := by
  exact void_baseStabilizes

example : ¬ baseStabilizes CoGame.Life := by
  exact life_not_baseStabilizes

example :
    detectsObstruction (witnessInterior_to_beliefState wi2) ↔
      hasCechOrContextualityObstruction wi2 := by
  exact interior_detects_obstruction_iff wi2

example :
    strictNoneismAdapter.interpretedImpossible (stabilizationFormula CoGame.Life) := by
  exact (noneist_objects_are_unstabilizable CoGame.Life).2 life_not_baseStabilizes

example :
    permissiveNoneismAdapter.interpretedClaim (stabilizationFormula CoGame.Life) := by
  exact life_noneist_bridge.2

end HeytingLean.Tests.Genesis

