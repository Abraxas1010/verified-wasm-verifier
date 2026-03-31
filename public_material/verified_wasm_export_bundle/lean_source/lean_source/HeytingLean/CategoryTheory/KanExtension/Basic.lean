import HeytingLean.Topos.LocSys.BaseChange

namespace HeytingLean
namespace CategoryTheory
namespace KanExtension

open _root_.CategoryTheory

universe uK uB vB

variable {K : Type uK} [CommRing K]
variable {X Y : Grpd.{vB, uB}}

noncomputable def pushforwardLocalSystem (f : X ⥤ Y) :
    Topos.LocSys.LocalSystem (K := K) X ⥤ Topos.LocSys.LocalSystem (K := K) Y :=
  Topos.LocSys.LocalSystems.pushforward (K := K) f

abbrev pullbackLocalSystem (f : X ⥤ Y) :
    Topos.LocSys.LocalSystem (K := K) Y ⥤ Topos.LocSys.LocalSystem (K := K) X :=
  Topos.LocSys.LocalSystems.pullback (K := K) f

/-- Real left-Kan base-change adjunction for local systems. -/
noncomputable def pushforwardAdjunction (f : X ⥤ Y) :
    pushforwardLocalSystem (K := K) f ⊣ pullbackLocalSystem (K := K) f := by
  simpa [pushforwardLocalSystem, pullbackLocalSystem] using
    Topos.LocSys.LocalSystems.pushforwardAdjunction (K := K) f

/-- Pullback is defined by precomposition. -/
theorem pullback_obj_eq_precompose (f : X ⥤ Y)
    (V : Topos.LocSys.LocalSystem (K := K) Y) :
    (pullbackLocalSystem (K := K) f).obj V = f ⋙ V := by
  rfl

end KanExtension
end CategoryTheory
end HeytingLean
