import HeytingLean.LoF.CryptoSheaf.Site
import HeytingLean.Topos.SheafBridges

namespace HeytingLean.HeytingVeil.Site

open HeytingLean.LoF.CryptoSheaf

universe u

/-- Restriction operator alias for PosetSite-based HeytingVeil semantics. -/
def restrictAlong {C : Type u} [PartialOrder C]
    (S : PosetSite C) {U V : C} (h : V ≤ U) :
    S.Logic U → S.Logic V :=
  S.restrict h

/-- First site theorem: identity restriction is definitional. -/
theorem restrictAlong_id {C : Type u} [PartialOrder C]
    (S : PosetSite C) (U : C) (x : S.Logic U) :
    restrictAlong S (U := U) (V := U) (le_rfl : U ≤ U) x = x :=
  S.restrict_id U x

/-- First site theorem: restriction composition follows site composition law. -/
theorem restrictAlong_comp {C : Type u} [PartialOrder C]
    (S : PosetSite C) {U V W : C} (hVU : V ≤ U) (hWV : W ≤ V) (x : S.Logic U) :
    restrictAlong S (U := V) (V := W) hWV (restrictAlong S (U := U) (V := V) hVU x) =
      restrictAlong S (U := U) (V := W) (le_trans hWV hVU) x :=
  S.restrict_comp hVU hWV x

end HeytingLean.HeytingVeil.Site

