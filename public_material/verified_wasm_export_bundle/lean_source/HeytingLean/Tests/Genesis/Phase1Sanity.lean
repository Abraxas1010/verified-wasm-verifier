import HeytingLean.Genesis

/-!
# Genesis Phase 1 Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open CoGame

#check CoGame
#check CoGame.Bisim
#check CoGame.bisim_refl
#check CoGame.ofPGame
#check IsSimulation
#check Sim
#check sim_le_refl
#check sim_le_trans
#check emergentLe
#check emergent_le_refl
#check phaseI
#check phaseJ
#check evalLife
#check life_is_self_referential
#check Void

example : Iterant.shift phaseI = phaseJ := by
  exact phaseJ_eq_shift_phaseI.symm

example : CoGame.Bisim CoGame.Life CoGame.Life := CoGame.life_bisim_self

example : Sim CoGame.Life CoGame.Life := sim_le_refl CoGame.Life

example :
    emergentLe (toEmergentClass CoGame.Life) (toEmergentClass CoGame.Life) :=
  emergent_le_refl (toEmergentClass CoGame.Life)

end HeytingLean.Tests.Genesis
