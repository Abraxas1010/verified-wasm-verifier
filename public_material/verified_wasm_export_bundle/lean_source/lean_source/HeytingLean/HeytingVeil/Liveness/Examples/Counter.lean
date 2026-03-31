import HeytingLean.HeytingVeil.Liveness.FairCycle

namespace HeytingLean
namespace HeytingVeil
namespace Liveness
namespace Examples

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.ModelCheck

def counterToThree : Machine Nat where
  Init := fun s => s = 0
  Step := fun s t => if s < 3 then t = s + 1 else t = 3

def counterToThreeDM : DecidableMachine Nat :=
  {
    machine := counterToThree
    states := [0, 1, 2, 3]
    decInit := by
      intro s
      simpa [counterToThree] using (inferInstance : Decidable (s = 0))
    decStep := by
      intro s t
      by_cases hlt : s < 3
      · simpa [counterToThree, hlt] using (inferInstance : Decidable (t = s + 1))
      · simpa [counterToThree, hlt] using (inferInstance : Decidable (t = 3))
  }

def reachesThree (s : Nat) : Prop := s = 3
instance : DecidablePred reachesThree := by
  intro s
  simpa [reachesThree] using (inferInstance : Decidable (s = 3))

#eval kLivenessCheck counterToThreeDM reachesThree 6

def deadLoop : Machine Nat where
  Init := fun s => s = 0
  Step := fun s t => s = 0 ∧ t = 0

def deadLoopDM : DecidableMachine Nat :=
  {
    machine := deadLoop
    states := [0]
    decInit := by
      intro s
      simpa [deadLoop] using (inferInstance : Decidable (s = 0))
    decStep := by
      intro s t
      simpa [deadLoop] using (inferInstance : Decidable (s = 0 ∧ t = 0))
  }

def reachesOne (s : Nat) : Prop := s = 1
instance : DecidablePred reachesOne := by
  intro s
  simpa [reachesOne] using (inferInstance : Decidable (s = 1))

#eval kLivenessCheck deadLoopDM reachesOne 6
#eval fairCycleCheck deadLoopDM 12 "weak"

end Examples
end Liveness
end HeytingVeil
end HeytingLean
