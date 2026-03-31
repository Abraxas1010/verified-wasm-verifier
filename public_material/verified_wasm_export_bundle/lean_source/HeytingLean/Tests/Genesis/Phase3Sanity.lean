import HeytingLean.Genesis

/-!
# Genesis Phase 3 Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open CoGame

#check unroll
#check unroll_zero_life
#check interpret_unroll_life_anchor
#check collapseNucleus
#check regionNucleus
#check EmergentFixed
#check LoFFixed
#check emergent_to_lof_fixed
#check lof_to_emergent_fixed
#check fixed_map_inf
#check fixed_map_top
#check fixed_map_equiv_or_embedding
#check WitnessInterior
#check toLensSection
#check toBeliefState
#check stabilization_compatibility

example : unroll 0 CoGame.Life = (0 : SetTheory.PGame) := by
  exact unroll_zero_life

example : oscillationExpr CoGame.Life = .reentry := by
  exact oscillationExpr_life

example (n : Nat) :
    interpretUnroll n (unroll n CoGame.Life) = nesting n := by
  exact interpret_unroll_life_anchor n

def wi0 : WitnessInterior := lifeInterior 0

example : wi0.depth = 1 := by
  rfl

example : collapseNucleus (toBeliefState wi0).support = (toBeliefState wi0).support := by
  exact stabilization_compatibility wi0

example : ((emergent_to_lof_fixed emergent_fixed_top : LoFFixed) : EmergentRegion) = Set.univ := by
  simpa using fixed_map_top_val

end HeytingLean.Tests.Genesis
