import HeytingLean.LoF.CuTe.Generate
import HeytingLean.Layouts.Flat.Tractable

/-!
# Sheaf bridge: LoF ↔ CuTe correspondence (bundle slice)

This module records a (currently simplified) “sheaf condition” view of the
tractability predicate for CuTe layouts.

For the purposes of the bundle, we treat the sheaf condition as a *named alias*
for tractability, so downstream files can use the intended terminology without
needing the full Grothendieck-topology development yet.
-/

namespace HeytingLean
namespace LoF
namespace CuTe

open HeytingLean.Layouts
open HeytingLean.Layouts.Flat

/-- A cover in the (toy) layout site. -/
structure LayoutCover (L : FlatLayout) where
  covers : List FlatLayout
  refines : ∀ c ∈ covers, FlatLayout.size c ≤ FlatLayout.size L

/-- Sheaf condition predicate (currently: alias for tractability). -/
def satisfiesSheafCondition (L : FlatLayout) : Prop :=
  FlatLayout.Tractable L

/-- Tractability implies the (bundle) sheaf condition. -/
theorem tractable_implies_sheaf (L : FlatLayout) (h : FlatLayout.Tractable L) :
    satisfiesSheafCondition L :=
  h

/-- Bundle correspondence theorem: tractability iff sheaf condition.

This is definitional for now; the intention is to replace `satisfiesSheafCondition`
with a genuine gluing predicate in later work.
-/
theorem tractability_iff_sheaf (L : FlatLayout) :
    FlatLayout.Tractable L ↔ satisfiesSheafCondition L :=
  Iff.rfl

end CuTe
end LoF
end HeytingLean

