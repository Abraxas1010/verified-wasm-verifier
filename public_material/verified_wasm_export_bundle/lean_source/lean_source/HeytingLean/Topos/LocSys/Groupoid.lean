import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.SingleObj

namespace HeytingLean
namespace Topos
namespace LocSys

open CategoryTheory

universe u

namespace Base1

universe v

/-- Product of two bundled groupoids (implemented as the product type). -/
abbrev prod (X Y : Grpd.{v, u}) : Grpd.{v, u} :=
  Grpd.of (X × Y)

/-- `BG` for a group `G`: the one-object groupoid with endomorphisms `G`. -/
abbrev BG (G : Type v) [Group G] : Grpd.{v, 0} :=
  Grpd.of (SingleObj G)

end Base1

end LocSys
end Topos
end HeytingLean
