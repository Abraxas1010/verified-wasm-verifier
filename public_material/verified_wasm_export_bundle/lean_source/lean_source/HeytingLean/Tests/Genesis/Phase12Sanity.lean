import HeytingLean.Genesis.Extensions

/-!
# Genesis Phase 12 Sanity

QM/QFT extension-interface checks.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open HeytingLean.Genesis.Extensions

#check minimalPrecondition
#check witnessInterior_toQMInterface
#check witnessInterior_toQFTInterface
#check qft_bridge_strict_policy

def wi3 : WitnessInterior := lifeInterior 3

example : minimalPrecondition wi3 := by
  exact minimalPrecondition_holds wi3

example : TriangleObstruction := by
  exact witnessInterior_toQMInterface_obstruction wi3

example :
    ¬ HeytingLean.PerspectivalPlenum.Extensions.QFTTrack.policyAllowsCounterterms
      (witnessInterior_toQFTInterface wi3).scaffold := by
  exact witnessInterior_toQFTInterface_counterterms_disallowed wi3

end HeytingLean.Tests.Genesis
