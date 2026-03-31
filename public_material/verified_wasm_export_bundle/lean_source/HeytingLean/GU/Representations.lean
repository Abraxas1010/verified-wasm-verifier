import HeytingLean.GU.Bundles

/-!
# GU.Representations (minimal)

Matter fields are often described as sections of associated bundles for a group action.
We model just enough structure to name this idea.
-/

namespace HeytingLean
namespace GU

universe u v w

/-!
We represent “a representation of `G` on `V`” as a `MulAction`.  This is intentionally minimal
and works for both finite- and infinite-dimensional settings (the extra linear/topological
structure can be added as additional typeclass assumptions in later phases).
-/

class Representation (G : Type u) (V : Type v) [Monoid G] extends MulAction G V

end GU
end HeytingLean
