import HeytingLean.Topos.LocSys.ChainComplexes
import HeytingLean.Topos.LocSys.Groupoid

import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Whiskering

namespace HeytingLean
namespace Topos
namespace LocSys

open CategoryTheory

universe uK uB vB

/-- `K`-linear local systems over a base groupoid `X`: functors `X ⥤ Coeff K`. -/
abbrev LocalSystem (K : Type uK) [CommRing K] (X : Grpd.{vB, uB}) : Type _ :=
  X ⥤ Coeff K

namespace LocalSystems

variable {K : Type uK} [CommRing K]
variable {X Y Z : Grpd.{vB, uB}}

/-- Pullback (base-change) of local systems along `f : X ⥤ Y` by precomposition. -/
abbrev pullback (f : X ⥤ Y) : LocalSystem K Y ⥤ LocalSystem K X :=
  (CategoryTheory.Functor.whiskeringLeft X Y (Coeff K)).obj f

@[simp]
theorem pullback_obj (f : X ⥤ Y) (V : LocalSystem K Y) :
    (pullback (K := K) f).obj V = f ⋙ V :=
  rfl

end LocalSystems

end LocSys
end Topos
end HeytingLean
