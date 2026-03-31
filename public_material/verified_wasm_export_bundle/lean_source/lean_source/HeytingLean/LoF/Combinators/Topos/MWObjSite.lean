import HeytingLean.LoF.Combinators.Category.MultiwayCategory
import HeytingLean.LoF.Combinators.Topos.ClosedSievesHeyting

import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# MWObjSite — a Grothendieck topology on the non-thin multiway path category

Phase C asks whether we can place a “topos/nucleus layer” on the **non-thin** multiway path
category `MWObj` (whose morphisms are labeled multi-step paths).

This file installs the minimal local infrastructure: we choose the *dense* Grothendieck topology
on `MWObj` (available on any category) and thereby obtain closed sieves as a Heyting algebra, just
as for the thin reachability site.

Objectivity boundary:
* This is an infrastructure layer only: we do **not** claim it is the “correct” topology for any
  physical/computational semantics beyond the generic dense-topology construction.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

/-- The dense Grothendieck topology on the non-thin multiway path category `MWObj`. -/
def mwDenseTopology : GrothendieckTopology MWObj :=
  GrothendieckTopology.dense

end Topos
end Combinators
end LoF
end HeytingLean

