import HeytingLean.HeytingVeil.Integration.WiringSite
import HeytingLean.HeytingVeil.Monadic.RNucleusBridge

namespace HeytingLean.HeytingVeil.Integration

open HeytingLean.Rel
open HeytingLean.HeytingVeil.Site
open HeytingLean.HeytingVeil.Monadic
open HeytingLean.LoF.CryptoSheaf

universe u

/-- Gate-controlled site wiring relation, keyed by the monadic option-lane position type. -/
def gatedSiteWire {C : Type u} [PartialOrder C]
    (S : PosetSite C) (U : C) (gate : Bool) :
    HRel (S.Logic U) (S.Logic U) :=
  if gate then siteOrderWire S U else fun _ _ => True

/-- The option-lane gate type is `Bool` (exposed here for cross-lane rewriting). -/
theorem optionGatePosEqBool : (optionLanePoly Unit).pos = Bool :=
  optionLanePosBool Unit

/-- Restriction preserves gated site wiring for both monadic gate branches. -/
theorem restrictAlong_preserves_gatedSiteWire {C : Type u} [PartialOrder C]
    (S : PosetSite C) {U V : C} (h : V ≤ U)
    (gate : Bool)
    {x y : S.Logic U}
    (hxy : gatedSiteWire S U gate x y) :
    gatedSiteWire S V gate (restrictAlong S h x) (restrictAlong S h y) := by
  cases gate with
  | false =>
      simp [gatedSiteWire]
  | true =>
      have hxyOrder : siteOrderWire S U x y := by
        simpa [gatedSiteWire] using hxy
      have hpres :=
        restrictAlong_preserves_siteOrderWire (S := S) (h := h) (x := x) (y := y) hxyOrder
      simpa [gatedSiteWire] using hpres

/-- Typed bridge from the monadic option-lane position type into gated site wiring preservation. -/
theorem restrictAlong_preserves_optionGateWire {C : Type u} [PartialOrder C]
    (S : PosetSite C) {U V : C} (h : V ≤ U)
    (gate : (optionLanePoly Unit).pos)
    {x y : S.Logic U}
    (hxy : gatedSiteWire S U (cast optionGatePosEqBool gate) x y) :
    gatedSiteWire S V (cast optionGatePosEqBool gate) (restrictAlong S h x) (restrictAlong S h y) := by
  simpa [optionGatePosEqBool] using
    (restrictAlong_preserves_gatedSiteWire (S := S) (h := h) (gate := cast optionGatePosEqBool gate)
      (x := x) (y := y) hxy)

end HeytingLean.HeytingVeil.Integration
