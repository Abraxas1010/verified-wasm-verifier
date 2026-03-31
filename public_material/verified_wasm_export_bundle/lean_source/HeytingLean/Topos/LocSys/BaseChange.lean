import HeytingLean.Topos.LocSys.LocalSystems

import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

namespace HeytingLean
namespace Topos
namespace LocSys

open CategoryTheory

universe uK uB vB

namespace LocalSystems

variable {K : Type uK} [CommRing K]
variable {X Y : Grpd.{vB, uB}}

/--
Pushforward of local systems along `f : X ⥤ Y`, implemented as left Kan extension.

This is a v1 semantics-level operation: it uses the existence of colimits in `ModuleCat K`.
-/
noncomputable def pushforward (f : X ⥤ Y) : LocalSystem (K := K) X ⥤ LocalSystem (K := K) Y := by
  classical
  -- `ModuleCat K` has all colimits, hence all these left Kan extensions exist.
  letI : ∀ (F : X ⥤ Coeff K), f.HasLeftKanExtension F := by
    intro F
    infer_instance
  exact f.lan (H := Coeff K)

/-- Unit for the `pushforward ⊣ pullback` adjunction (left Kan extension adjunction). -/
noncomputable def pushforwardUnit (f : X ⥤ Y) :
    𝟭 (LocalSystem (K := K) X) ⟶
      pushforward (K := K) f ⋙ (CategoryTheory.Functor.whiskeringLeft X Y (Coeff K)).obj f := by
  classical
  letI : ∀ (F : X ⥤ Coeff K), f.HasLeftKanExtension F := by
    intro F
    infer_instance
  exact f.lanUnit (H := Coeff K)

/-- `pushforward f` is left adjoint to pullback by precomposition. -/
noncomputable def pushforwardAdjunction (f : X ⥤ Y) :
    pushforward (K := K) f ⊣ pullback (K := K) f := by
  classical
  letI : ∀ (F : X ⥤ Coeff K), f.HasLeftKanExtension F := by
    intro F
    infer_instance
  simpa [pullback, pushforward] using (f.lanAdjunction (H := Coeff K))

end LocalSystems

end LocSys
end Topos
end HeytingLean
