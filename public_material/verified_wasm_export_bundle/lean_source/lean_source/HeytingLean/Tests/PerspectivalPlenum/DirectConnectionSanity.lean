import HeytingLean.PerspectivalPlenum.DirectConnection

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open CategoryTheory

universe u v w

variable {Ωα : Type u} [HeytingLean.LoF.PrimaryAlgebra Ωα]
variable {C : Type v} [Category.{w} C]
variable [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]

#check HeytingLean.PerspectivalPlenum.RatchetStep
#check HeytingLean.PerspectivalPlenum.ReentryLTBridge

#check HeytingLean.PerspectivalPlenum.ReentryLTBridge.reentry_fixed_iff_reclassify_fixed
#check HeytingLean.PerspectivalPlenum.ReentryLTBridge.reentry_fixed_iff_isClosed_omega
#check HeytingLean.PerspectivalPlenum.ReentryLTBridge.map_reentry_fixed_to_closed
#check HeytingLean.PerspectivalPlenum.ReentryLTBridge.closed_to_reentry_fixed

end PerspectivalPlenum
end Tests
end HeytingLean
