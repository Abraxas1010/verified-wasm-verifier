import HeytingLean.Genesis

/-!
# Genesis Phase 7 Sanity

Regression checks for concrete transport adapters into `ReentryLTBridge`.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open CategoryTheory

section

universe u v w

variable {Ωα : Type u} [HeytingLean.LoF.PrimaryAlgebra Ωα]
variable {C : Type v} [Category.{w} C]
variable [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]

variable (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
variable (seed : ConcreteBridgeSeed B)
variable (W : WitnessInterior)

#check witnessInterior_transport_data
#check transport_stable_fixed
#check transport_unstable_not_fixed
#check transport_reentry_fixed_to_closed
#check transport_closed_to_reentry_fixed
#check transport_compat_with_stabilization
#check minimalDistinction_existsInPlenum
#check minimalDistinction_not_collapse_in_emergentLens
#check emergent_region_transport_data
#check emergent_region_transport_compat_with_stabilization
#check emergent_region_transport_life_not_fixed
#check emergent_region_transport_cantor_true_fixed
#check emergent_region_transport_cantor_false_not_fixed

example :
    eventualStabilizes W.source ↔
      B.R.nucleus (witnessInterior_transport_data B seed W)
        = witnessInterior_transport_data B seed W := by
  exact transport_compat_with_stabilization (B := B) (seed := seed) (W := W)

example : PerspectivalPlenum.LensSheaf.ExistsInPlenum minimalDistinction := by
  exact minimalDistinction_existsInPlenum

example :
    ¬ PerspectivalPlenum.Lens.CollapseToBottom emergentRegionLens minimalDistinction := by
  exact minimalDistinction_not_collapse_in_emergentLens

example :
    regionNucleus (emergent_region_transport_data (lifeInterior 0))
      ≠ emergent_region_transport_data (lifeInterior 0) := by
  exact emergent_region_transport_life_not_fixed

example (p : EvalPath) (h0 : p 0 = true) :
    regionNucleus (emergent_region_transport_data (cantorCut_to_witnessInterior p 0))
      = emergent_region_transport_data (cantorCut_to_witnessInterior p 0) := by
  exact emergent_region_transport_cantor_true_fixed p h0

example (p : EvalPath) (h0 : p 0 = false) :
    regionNucleus (emergent_region_transport_data (cantorCut_to_witnessInterior p 0))
      ≠ emergent_region_transport_data (cantorCut_to_witnessInterior p 0) := by
  exact emergent_region_transport_cantor_false_not_fixed p h0

end

end HeytingLean.Tests.Genesis
