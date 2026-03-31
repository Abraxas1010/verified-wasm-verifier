import HeytingLean.HeytingVeil.Package.CABLink

namespace HeytingLean.HeytingVeil.Package

open HeytingLean.HeytingVeil

inductive VerificationStatus
  | certified
  | unverified (reason : String)
  deriving Repr, DecidableEq

def verifyExport (route : Route.RouteRecord) (payload : CabPayload) : VerificationStatus :=
  if route.certifiedRequested
      && (!Route.isImplementedRouteClass route.routeClassId)
      && route.preservationWitnessIds.isEmpty then
    .unverified "planned route not yet certified"
  else if route.certifiedRequested
      && (!Route.isImplementedRouteClass route.routeClassId) then
    .unverified "route class not rollout-enabled"
  else if route.certifiedRequested
      && Route.isPreviewRouteClass route.routeClassId
      && route.previewPromotionCertified
      && route.previewPromotionReady
      && payload.certified then
    .certified
  else if route.certifiedRequested
      && Route.isPreviewRouteClass route.routeClassId
      && route.previewPromotionReady then
    .unverified "preview route awaiting certifying promotion"
  else if route.certifiedRequested
      && Route.isPreviewRouteClass route.routeClassId then
    .unverified "preview route not yet certified"
  else if route.certifiedRequested && route.preservationWitnessIds.isEmpty then
    .unverified "missing route preservation witness"
  else if payload.certified then
    .certified
  else
    .unverified "not certified by route policy"

/-- Sprint obligation `HV.Package.PlannedRouteDowngradesUnverified`. -/
theorem plannedRouteDowngradesUnverified
    (route : Route.RouteRecord) (payload : CabPayload)
    (hReq : route.certifiedRequested = true)
    (hNotImplemented : Route.isImplementedRouteClass route.routeClassId = false)
    (hEmpty : route.preservationWitnessIds.isEmpty = true) :
    verifyExport route payload = .unverified "planned route not yet certified" := by
  unfold verifyExport
  simp [hReq, hNotImplemented, hEmpty]

/-- Sprint obligation `HV.Package.NotImplementedRouteDowngradesUnverified`. -/
theorem notImplementedRouteDowngradesUnverified
    (route : Route.RouteRecord) (payload : CabPayload)
    (hReq : route.certifiedRequested = true)
    (hNotImplemented : Route.isImplementedRouteClass route.routeClassId = false) :
    verifyExport route payload = .unverified "route class not rollout-enabled"
      ∨ verifyExport route payload = .unverified "planned route not yet certified" := by
  by_cases hEmpty : route.preservationWitnessIds.isEmpty = true
  · right
    exact plannedRouteDowngradesUnverified route payload hReq hNotImplemented hEmpty
  · left
    unfold verifyExport
    simp [hReq, hNotImplemented, hEmpty]

/-- Sprint obligation `HV.Package.MissingWitnessDowngradesUnverified`. -/
theorem missingWitnessDowngradesUnverified
    (route : Route.RouteRecord) (payload : CabPayload)
    (hReq : route.certifiedRequested = true)
    (hImplemented : Route.isImplementedRouteClass route.routeClassId = true)
    (hNotPreview : Route.isPreviewRouteClass route.routeClassId = false)
    (hEmpty : route.preservationWitnessIds.isEmpty = true) :
    verifyExport route payload = .unverified "missing route preservation witness" := by
  unfold verifyExport
  simp [hReq, hImplemented, hNotPreview, hEmpty]

/-- Sprint obligation `HV.Package.PreviewRouteDowngradesUnverified`. -/
theorem previewRouteDowngradesUnverified
    (route : Route.RouteRecord) (payload : CabPayload)
    (hReq : route.certifiedRequested = true)
    (hPreview : Route.isPreviewRouteClass route.routeClassId = true)
    (hNotPromoted : route.previewPromotionCertified = false)
    (hNotReady : route.previewPromotionReady = false) :
    verifyExport route payload = .unverified "preview route not yet certified" := by
  have hImplemented : Route.isImplementedRouteClass route.routeClassId = true := by
    exact Route.previewRouteClassImplementedFromFlag route.routeClassId hPreview
  unfold verifyExport
  simp [hReq, hImplemented, hPreview, hNotPromoted, hNotReady]

/-- Sprint obligation `HV.Package.PreviewRouteReadyDowngradesPromotionReason`. -/
theorem previewRouteReadyDowngradesPromotionReason
    (route : Route.RouteRecord) (payload : CabPayload)
    (hReq : route.certifiedRequested = true)
    (hPreview : Route.isPreviewRouteClass route.routeClassId = true)
    (hNotPromoted : route.previewPromotionCertified = false)
    (hReady : route.previewPromotionReady = true) :
    verifyExport route payload = .unverified "preview route awaiting certifying promotion" := by
  have hImplemented : Route.isImplementedRouteClass route.routeClassId = true := by
    exact Route.previewRouteClassImplementedFromFlag route.routeClassId hPreview
  unfold verifyExport
  simp [hReq, hImplemented, hPreview, hNotPromoted, hReady]

/-- Sprint obligation `HV.Package.CertifiedWhenNoMissingWitnessAndPayloadCertified`. -/
theorem certifiedWhenNoMissingWitnessAndPayloadCertified
    (route : Route.RouteRecord) (payload : CabPayload)
    (hRolloutGate : (route.certifiedRequested
      && (!Route.isImplementedRouteClass route.routeClassId)) = false)
    (hPreviewGate : (route.certifiedRequested
      && Route.isPreviewRouteClass route.routeClassId) = false)
    (hMissing : (route.certifiedRequested && route.preservationWitnessIds.isEmpty) = false)
    (hCert : payload.certified = true) :
    verifyExport route payload = .certified := by
  unfold verifyExport
  simp [hRolloutGate, hPreviewGate, hMissing, hCert]

/-- Sprint obligation `HV.Package.PolicyDowngradeWhenNoMissingWitnessAndPayloadUncertified`. -/
theorem policyDowngradeWhenNoMissingWitnessAndPayloadUncertified
    (route : Route.RouteRecord) (payload : CabPayload)
    (hRolloutGate : (route.certifiedRequested
      && (!Route.isImplementedRouteClass route.routeClassId)) = false)
    (hPreviewGate : (route.certifiedRequested
      && Route.isPreviewRouteClass route.routeClassId) = false)
    (hMissing : (route.certifiedRequested && route.preservationWitnessIds.isEmpty) = false)
    (hCert : payload.certified = false) :
    verifyExport route payload = .unverified "not certified by route policy" := by
  unfold verifyExport
  simp [hRolloutGate, hPreviewGate, hMissing, hCert]

/-- Sprint obligation `HV.Package.SelectedCompatibleCertRequestedIsCertified`. -/
theorem selectedCompatibleCertRequestedIsCertified
    (m : DSL.Module)
    (art : DSL.LeanArtifact)
    (route : Route.BackendRoute)
    (hHint : Route.parseBackendHint m.backendHint = some route)
    (hCompat : Route.routeSupportsTarget route m.backendTarget = true)
    (hReq : m.packageCertificate = "cab_export_v2") :
    verifyExport
      (Route.select m).record
      (bindCabPayload art (Route.select m).record 17) = .certified := by
  have hReq' : (Route.select m).record.certifiedRequested = true := by
    simpa [hReq] using Route.certRequestFromPackageCertificate m
  have hClass : (Route.select m).record.routeClassId = Route.routeClassIdFor route := by
    unfold Route.select
    simp [hHint]
  have hImplemented : Route.isImplementedRouteClass (Route.select m).record.routeClassId = true := by
    simpa [hClass] using Route.routeClassIdForImplemented route
  have hRolloutGate : ((Route.select m).record.certifiedRequested
      && (!Route.isImplementedRouteClass (Route.select m).record.routeClassId)) = false := by
    simp [hReq', hImplemented]
  have hNotPreview : Route.isPreviewRouteClass (Route.select m).record.routeClassId = false := by
    simpa [hClass] using Route.routeClassIdForNotPreview route
  have hPreviewGate : ((Route.select m).record.certifiedRequested
      && Route.isPreviewRouteClass (Route.select m).record.routeClassId) = false := by
    simp [hReq', hNotPreview]
  have hWitness : ((Route.select m).record.preservationWitnessIds).isEmpty = false :=
    Route.selectedCompatibleHasWitnesses m route hHint hCompat
  have hMissing : ((Route.select m).record.certifiedRequested
      && ((Route.select m).record.preservationWitnessIds).isEmpty) = false := by
    simp [hReq', hWitness]
  have hCert : (bindCabPayload art (Route.select m).record 17).certified = true := by
    simp [bindCabPayload, Route.canCertify, hReq', hWitness]
  exact certifiedWhenNoMissingWitnessAndPayloadCertified
    (Route.select m).record
    (bindCabPayload art (Route.select m).record 17)
    hRolloutGate
    hPreviewGate
    hMissing
    hCert

/-- Sprint obligation `HV.Package.SelectedIncompatibleCertRequestedDowngradesMissingWitness`. -/
theorem selectedIncompatibleCertRequestedDowngradesMissingWitness
    (m : DSL.Module)
    (art : DSL.LeanArtifact)
    (route : Route.BackendRoute)
    (hHint : Route.parseBackendHint m.backendHint = some route)
    (hCompat : Route.routeSupportsTarget route m.backendTarget = false)
    (hReq : m.packageCertificate = "cab_export_v2") :
    verifyExport
      (Route.select m).record
      (bindCabPayload art (Route.select m).record 17)
      = .unverified "missing route preservation witness" := by
  have hReq' : (Route.select m).record.certifiedRequested = true := by
    simpa [hReq] using Route.certRequestFromPackageCertificate m
  have hClass : (Route.select m).record.routeClassId = Route.routeClassIdFor route := by
    unfold Route.select
    simp [hHint]
  have hImplemented : Route.isImplementedRouteClass (Route.select m).record.routeClassId = true := by
    simpa [hClass] using Route.routeClassIdForImplemented route
  have hNotPreview : Route.isPreviewRouteClass (Route.select m).record.routeClassId = false := by
    simpa [hClass] using Route.routeClassIdForNotPreview route
  have hWitness : (Route.select m).record.preservationWitnessIds = [] :=
    Route.selectedWitnessIdsEmptyForIncompatibleRoute m route hHint hCompat
  have hEmpty : ((Route.select m).record.preservationWitnessIds).isEmpty = true := by
    simp [hWitness]
  exact missingWitnessDowngradesUnverified
    (Route.select m).record
    (bindCabPayload art (Route.select m).record 17)
    hReq'
    hImplemented
    hNotPreview
    hEmpty

/-- Sprint obligation `HV.Package.SelectedPlannedCertRequestedDowngradesPlannedReason`. -/
theorem selectedPlannedCertRequestedDowngradesPlannedReason
    (m : DSL.Module)
    (art : DSL.LeanArtifact)
    (hParse : Route.parseBackendHint m.backendHint = none)
    (hPlanned : Route.isPlannedRouteClass m.backendHint = true)
    (hReq : m.packageCertificate = "cab_export_v2") :
    verifyExport
      (Route.select m).record
      (bindCabPayload art (Route.select m).record 17)
      = .unverified "planned route not yet certified" := by
  have hReq' : (Route.select m).record.certifiedRequested = true := by
    simpa [hReq] using Route.certRequestFromPackageCertificate m
  have hNotImplemented : Route.isImplementedRouteClass (Route.select m).record.routeClassId = false := by
    have hRouteImpl : (Route.select m).routeImplemented = false :=
      (Route.selectedPlannedHintRecognizedUnimplemented m hParse hPlanned).2.1
    have hImplEq := Route.selectedRouteImplementedMatchesClassPolicy m
    calc
      Route.isImplementedRouteClass (Route.select m).record.routeClassId
          = (Route.select m).routeImplemented := by
            simpa using hImplEq.symm
      _ = false := hRouteImpl
  have hEmpty : ((Route.select m).record.preservationWitnessIds).isEmpty = true := by
    unfold Route.select
    simp [hParse]
  exact plannedRouteDowngradesUnverified
    (Route.select m).record
    (bindCabPayload art (Route.select m).record 17)
    hReq'
    hNotImplemented
    hEmpty

/-- Sprint obligation `HV.Package.SelectedPreviewCertRequestedDowngradesPreviewReason`. -/
theorem selectedPreviewCertRequestedDowngradesPreviewReason
    (m : DSL.Module)
    (art : DSL.LeanArtifact)
    (hParse : Route.parseBackendHint m.backendHint = none)
    (hPreview : Route.isPreviewRouteClass m.backendHint = true)
    (hReq : m.packageCertificate = "cab_export_v2") :
    verifyExport
      (Route.select m).record
      (bindCabPayload art (Route.select m).record 17)
      = .unverified "preview route not yet certified"
        ∨ verifyExport
            (Route.select m).record
            (bindCabPayload art (Route.select m).record 17)
            = .unverified "preview route awaiting certifying promotion" := by
  have hReq' : (Route.select m).record.certifiedRequested = true := by
    simpa [hReq] using Route.certRequestFromPackageCertificate m
  have hPreview' : Route.isPreviewRouteClass (Route.select m).record.routeClassId = true := by
    rcases Route.selectedPreviewHintRecognizedImplemented m hParse hPreview with
      ⟨_, _, _, hClass, _, _, _, _, _⟩
    simpa [hClass] using hPreview
  have hNotPromoted : (Route.select m).record.previewPromotionCertified = false := by
    unfold Route.select
    simp [hParse]
  cases hReadyVal : (Route.select m).record.previewPromotionReady with
  | true =>
    right
    exact previewRouteReadyDowngradesPromotionReason
      (Route.select m).record
      (bindCabPayload art (Route.select m).record 17)
      hReq'
      hPreview'
      hNotPromoted
      hReadyVal
  | false =>
    left
    exact previewRouteDowngradesUnverified
      (Route.select m).record
      (bindCabPayload art (Route.select m).record 17)
      hReq'
      hPreview'
      hNotPromoted
      hReadyVal

/-- Sprint obligation `HV.Package.BindPayloadNeverHitsPolicyDowngradeReason`. -/
theorem bindPayloadNeverHitsPolicyDowngradeReason
    (route : Route.RouteRecord)
    (art : DSL.LeanArtifact) :
    verifyExport route (bindCabPayload art route 17)
      ≠ .unverified "not certified by route policy" := by
  unfold verifyExport bindCabPayload Route.canCertify
  cases hReq : route.certifiedRequested <;>
    cases hImpl : Route.isImplementedRouteClass route.routeClassId <;>
    cases hPreview : Route.isPreviewRouteClass route.routeClassId <;>
    cases hPromoted : route.previewPromotionCertified <;>
    cases hReady : route.previewPromotionReady <;>
    cases hEmpty : route.preservationWitnessIds.isEmpty <;>
    simp

end HeytingLean.HeytingVeil.Package
