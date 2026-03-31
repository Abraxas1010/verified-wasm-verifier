import HeytingLean.HeytingVeil.Wiring.Composition
import HeytingLean.HeytingVeil.Site.PosetBridge
import HeytingLean.Rel.Basic

namespace HeytingLean.HeytingVeil.Integration

open HeytingLean.Rel
open HeytingLean.HeytingVeil.Wiring
open HeytingLean.HeytingVeil.Site
open HeytingLean.LoF.CryptoSheaf

universe u

/-- Site-induced order relation interpreted as a wiring relation. -/
def siteOrderWire {C : Type u} [PartialOrder C]
    (S : PosetSite C) (U : C) : HRel (S.Logic U) (S.Logic U) :=
  fun x y => x ≤ y

/-- Cross-lane bridge theorem: composing site-order wiring collapses by transitivity. -/
theorem compose_siteOrderWire_eq {C : Type u} [PartialOrder C]
    (S : PosetSite C) (U : C) :
    composeWire (siteOrderWire S U) (siteOrderWire S U) = siteOrderWire S U := by
  funext x
  funext y
  apply propext
  constructor
  · intro h
    rcases h with ⟨m, hxm, hmy⟩
    exact le_trans hxm hmy
  · intro h
    exact ⟨x, le_rfl, h⟩

/-- Restriction maps preserve the site-order wiring relation. -/
theorem restrictAlong_preserves_siteOrderWire {C : Type u} [PartialOrder C]
    (S : PosetSite C) {U V : C} (h : V ≤ U)
    {x y : S.Logic U}
    (hxy : siteOrderWire S U x y) :
    siteOrderWire S V (restrictAlong S h x) (restrictAlong S h y) := by
  have hinf :
      S.restrictHom (U := U) (V := V) h x ⊓ S.restrictHom (U := U) (V := V) h y =
        S.restrictHom (U := U) (V := V) h x := by
    calc
      S.restrictHom (U := U) (V := V) h x ⊓ S.restrictHom (U := U) (V := V) h y =
          S.restrictHom (U := U) (V := V) h (x ⊓ y) := by
            symm
            exact map_inf (S.restrictHom (U := U) (V := V) h) x y
      _ = S.restrictHom (U := U) (V := V) h x := by
            simp [inf_eq_left.mpr hxy]
  have hmono : S.restrictHom (U := U) (V := V) h x ≤ S.restrictHom (U := U) (V := V) h y :=
    inf_eq_left.mp hinf
  simpa [siteOrderWire, restrictAlong, S.restrictHom_toFun h] using hmono

end HeytingLean.HeytingVeil.Integration
