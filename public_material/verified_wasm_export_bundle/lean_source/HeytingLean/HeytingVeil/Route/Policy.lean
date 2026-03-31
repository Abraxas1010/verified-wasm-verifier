import HeytingLean.HeytingVeil.Route.ClassRegistry

namespace HeytingLean.HeytingVeil.Route

/-- Route can be certified only when witness IDs are present. -/
def canCertify (r : RouteRecord) : Bool :=
  if r.certifiedRequested then
    !r.preservationWitnessIds.isEmpty
      || (isPreviewRouteClass r.routeClassId
          && r.previewPromotionCertified
          && r.previewPromotionReady)
  else
    true

/-- Sprint obligation `HV.Route.RequiresWitnessForCertified`. -/
theorem requiresWitnessForCertified (r : RouteRecord)
    (hReq : r.certifiedRequested = true)
    (hPreviewCertified : r.previewPromotionCertified = false)
    (hCan : canCertify r = true) :
    r.preservationWitnessIds.isEmpty = false := by
  unfold canCertify at hCan
  simp [hReq, hPreviewCertified] at hCan
  simpa [List.isEmpty_eq_false_iff] using hCan

end HeytingLean.HeytingVeil.Route
