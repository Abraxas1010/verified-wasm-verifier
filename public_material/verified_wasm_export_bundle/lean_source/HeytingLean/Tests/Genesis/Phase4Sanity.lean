import HeytingLean.Genesis

/-!
# Genesis Phase 4 Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open CoGame

#check witnessInterior_to_lensSection
#check witnessInterior_to_beliefState
#check interior_detects_obstruction
#check baseStabilizes
#check noneist_objects_are_unstabilizable
#check life_noneist_bridge
#check phasePoleI
#check phasePoleJ
#check minimalDistinction
#check minimalDistinction_def
#check bot_lt_minimalDistinction
#check minimalDistinction_atom
#check nucleus_extensive_floor

def wi1 : WitnessInterior := lifeInterior 1

example :
    detectsObstruction (witnessInterior_to_beliefState wi1) := by
  exact witnessInterior_detects_obstruction wi1

example :
    hasCechOrContextualityObstruction wi1 := by
  exact hasCechOrContextualityObstruction_intro wi1

example :
    ¬ baseStabilizes CoGame.Life := by
  exact life_not_baseStabilizes

example :
    strictNoneismAdapter.interpretedImpossible (stabilizationFormula CoGame.Life) := by
  exact (noneist_objects_are_unstabilizable CoGame.Life).2 life_not_baseStabilizes

example :
    strictNoneismAdapter.interpretedImpossible (stabilizationFormula CoGame.Life) ∧
      permissiveNoneismAdapter.interpretedClaim (stabilizationFormula CoGame.Life) := by
  exact life_noneist_bridge

example : minimalDistinction = phasePoleI ⊓ phasePoleJ := by
  exact minimalDistinction_def

example : (⊥ : EmergentRegion) < minimalDistinction := by
  exact bot_lt_minimalDistinction

example : IsAtom minimalDistinction := by
  exact minimalDistinction_atom

example (U : EmergentRegion) : regionLe U (regionNucleus U) := by
  exact nucleus_extensive_floor U

end HeytingLean.Tests.Genesis
