import HeytingLean.Genesis.Extensions

/-!
# Genesis Phase 14 Sanity

Deferred-closure checks for active-inference-specific witness adapters.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open HeytingLean.Genesis.Extensions

#check toActiveBeliefState
#check witnessInterior_toAgent
#check witnessInterior_freeEnergy_bounds_surprise
#check witnessInterior_expectedFreeEnergy_def
#check observationOfTernaryWitnessPoint
#check ternaryPoint_toActiveBeliefState
#check observationOfTernaryWitnessPoint_agrees_with_cantorCut
#check ternaryPoint_toActiveBeliefState_agrees_with_toActiveBeliefState
#check cantorSet_subtype_card_eq_continuum
#check evalPath_card_eq_ternaryCantorSubtype
#check evalPath_equiv_ternaryCantorSubtype

def wiLife : WitnessInterior := lifeInterior 2
def wiVoid : WitnessInterior := by
  refine
    { source := CoGame.Void
      depth := 1
      postReentry := Nat.succ_pos 0 }

def pTrue : EvalPath := fun _ => true
def pFalse : EvalPath := fun _ => false

example : witnessExpectedFreeEnergy wiLife = 0 := by
  exact witnessInterior_expectedFreeEnergy_def wiLife

example : witnessFreeEnergy wiLife ≥ witnessSurprise wiLife := by
  exact witnessInterior_freeEnergy_bounds_surprise wiLife

example : observationOf wiLife = WitnessObservation.unstable := by
  unfold observationOf wiLife lifeInterior
  simp [life_not_eventualStabilizes]

example : observationOf wiVoid = WitnessObservation.stable := by
  unfold observationOf wiVoid
  simp [void_eventualStabilizes]

example : observationOfTernaryWitnessPoint (evalPath_equiv_ternaryCantor_range pTrue)
    = WitnessObservation.stable := by
  simp [observationOfTernaryWitnessPoint_of_evalPath, pTrue]

example : observationOfTernaryWitnessPoint (evalPath_equiv_ternaryCantor_range pFalse)
    = WitnessObservation.unstable := by
  simp [observationOfTernaryWitnessPoint_of_evalPath, pFalse]

example : observationOfTernaryWitnessPoint (evalPath_equiv_ternaryCantor_range pFalse)
    = observationOf (cantorCut_to_witnessInterior pFalse 0) := by
  simpa using observationOfTernaryWitnessPoint_agrees_with_cantorCut pFalse 0

example :
    ternaryPoint_toActiveBeliefState
      (evalPath_equiv_ternaryCantor_range pTrue)
      (metaOfWitnessInterior (cantorCut_to_witnessInterior pTrue 1))
    = toActiveBeliefState (cantorCut_to_witnessInterior pTrue 1) := by
  simpa using ternaryPoint_toActiveBeliefState_agrees_with_toActiveBeliefState pTrue 1

example : Cardinal.mk ({x : ℝ // x ∈ cantorSet}) = Cardinal.continuum := by
  simpa using cantorSet_subtype_card_eq_continuum

end HeytingLean.Tests.Genesis
