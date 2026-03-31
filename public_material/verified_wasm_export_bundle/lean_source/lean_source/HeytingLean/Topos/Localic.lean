import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
Localic — optional bridge towards concrete examples.

This module provides a minimal sketch for a future bridge between
our LocalOperator abstraction and localic/topological settings. It keeps
compilation light and type-level only, so CI remains strict.

Intended use (later):
- Use `TopCat` and `Topology.Sheaves` for concrete sheaf examples.
- Show how nuclei/frames of opens can induce LocalOperator-like behavior.

For now, we expose only imports and a tiny section with type-level checks
to ensure we depend on the right mathlib APIs.
-/

namespace HeytingLean
namespace Topos
namespace Localic

open CategoryTheory

section
  universe u
  -- Type-level check: sheafification names exist for later use.
  variable (X : Type u) [TopologicalSpace X]
  #check TopCat
  -- The presheaf → sheaf functor (via Sites) exists; we will reuse it in examples.
  -- We avoid wiring concrete examples here to keep compile time small.
end

end Localic
end Topos
end HeytingLean
