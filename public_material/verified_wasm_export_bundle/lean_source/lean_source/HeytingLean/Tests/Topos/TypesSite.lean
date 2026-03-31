import HeytingLean.Topos.SheafBridges
import Mathlib.CategoryTheory.Sites.Grothendieck

namespace HeytingLean
namespace Tests
namespace Topos

/-! Sheaf smoke for the canonical category of types. -/

section
  universe u w
  -- The category of (small) types has a built-in category instance.
  variable (J : CategoryTheory.GrothendieckTopology (Type u))
  variable (A : Type w) [Category.{max u w} A]

  -- `Sheaf J A` exists over the site on `Type u`.
  #check CategoryTheory.Sheaf J A
  -- Our facade exposes the sheafification functor and adjunction on this site.
  #check HeytingLean.Topos.SheafBridges.presheafToSheaf (C := Type u) (A := A) J
  #check HeytingLean.Topos.SheafBridges.sheafificationAdjunction (C := Type u) (A := A) J
end

end Topos
end Tests
end HeytingLean

