import HeytingLean.HeytingVeil.DSL.Emit
import HeytingLean.HeytingVeil.Route.Policy
import HeytingLean.HeytingVeil.Route.Selection

namespace HeytingLean.HeytingVeil.Package

open HeytingLean.HeytingVeil

structure CabPayload where
  moduleName : String
  specHash : UInt64
  routeTag : String
  routeWitnessIds : List String
  artifactHash : UInt64
  certified : Bool
  deriving Repr, DecidableEq

def baseTheoremIds : List String :=
  [ "HeytingLean.HeytingVeil.Route.requiresWitnessForCertified"
  , "HeytingLean.HeytingVeil.Package.cabBindsSpecProofRouteHashes"
  , "HeytingLean.HeytingVeil.Package.missingWitnessDowngradesUnverified"
  ]

def theoremIdsForRoute (route : Route.RouteRecord) : List String :=
  baseTheoremIds ++ route.preservationWitnessIds

def theoremIdsForRouteTier (route : Route.BackendRoute) (tier : String) : List String :=
  baseTheoremIds ++ Route.witnessIdsFor route tier

def theoremIdsForRouteProfile (route : Route.BackendRoute) (profile : String) : List String :=
  theoremIdsForRouteTier route (Route.witnessTierForProfile profile)

def previewPromotionTheoremIdsForSelection
    (selection : Route.Selection) : List String :=
  if selection.record.previewPromotionCertified && selection.previewPromotionTransitionReady then
    selection.previewPromotionTransitionIds
  else
    []

def theoremIdsForSelection (selection : Route.Selection) : List String :=
  theoremIdsForRoute selection.record ++ previewPromotionTheoremIdsForSelection selection

def theoremContractIds : List String :=
  [ "HeytingLean.HeytingVeil.Package.theoremIdSelectionLength"
  , "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenCertifiedReady"
  , "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionLengthWhenCertifiedReady"
  , "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenNotCertified"
  ]

def theoremContractV2ProjectionGuardIds : List String :=
  [ "HeytingLean.HeytingVeil.Package.sharedTheoremContractIdsWithPolicySelectionSingleton"
  , "HeytingLean.HeytingVeil.Package.sharedTheoremContractIdsWithPolicyLength"
  ]

def theoremContractIdsForVersion (version : String) : List String :=
  if version = "v2" then
    theoremContractIds ++ theoremContractV2ProjectionGuardIds
  else
    theoremContractIds

def sharedTheoremContractIdsWithPolicy (classId : String) : List String :=
  (Route.promotionTransitionTheoremContractIds classId).filter (fun id => id ∈ theoremContractIds)

def sharedTheoremContractIdsWithPolicyForVersion (version classId : String) : List String :=
  (Route.promotionTransitionTheoremContractIdsForVersion version classId).filter
    (fun id => id ∈ theoremContractIdsForVersion version)

def bindCabPayload
    (art : DSL.LeanArtifact)
    (route : Route.RouteRecord)
    (specHash : UInt64) : CabPayload :=
  { moduleName := art.moduleName
    specHash := specHash
    routeTag := route.routeClassId
    routeWitnessIds := route.preservationWitnessIds
    artifactHash := art.contentHash
    certified := Route.canCertify route }

/-- Sprint obligation `HV.Package.CABBindsSpecProofRouteHashes`. -/
theorem cabBindsSpecProofRouteHashes
    (art : DSL.LeanArtifact)
    (route : Route.RouteRecord) :
    (bindCabPayload art route 17).artifactHash = art.contentHash := by
  simp [bindCabPayload]

/-- Sprint obligation `HV.Package.RouteWitnessTheoremIdsIncluded`. -/
theorem routeWitnessTheoremIdsIncluded
    (route : Route.RouteRecord) (w : String)
    (h : w ∈ route.preservationWitnessIds) :
    w ∈ theoremIdsForRoute route := by
  simp [theoremIdsForRoute, h]

/-- Sprint obligation `HV.Package.TheoremIdListLength`. -/
theorem theoremIdListLength
    (route : Route.RouteRecord) :
    (theoremIdsForRoute route).length
      = baseTheoremIds.length + route.preservationWitnessIds.length := by
  simp [theoremIdsForRoute]

/-- Sprint obligation `HV.Package.TheoremIdRouteTierLength`. -/
theorem theoremIdRouteTierLength
    (route : Route.BackendRoute) (tier : String) :
    (theoremIdsForRouteTier route tier).length
      = baseTheoremIds.length + (Route.witnessIdsFor route tier).length := by
  simp [theoremIdsForRouteTier]

/-- Sprint obligation `HV.Package.TheoremIdRouteProfileLength`. -/
theorem theoremIdRouteProfileLength
    (route : Route.BackendRoute) (profile : String) :
    (theoremIdsForRouteProfile route profile).length
      = baseTheoremIds.length
        + (Route.witnessIdsFor route (Route.witnessTierForProfile profile)).length := by
  simp [theoremIdsForRouteProfile, theoremIdsForRouteTier]

/-- Sprint obligation `HV.Package.PreviewPromotionTheoremIdsForSelectionWhenCertifiedReady`. -/
theorem previewPromotionTheoremIdsForSelectionWhenCertifiedReady
    (selection : Route.Selection)
    (hCertified : selection.record.previewPromotionCertified = true)
    (hReady : selection.previewPromotionTransitionReady = true) :
    previewPromotionTheoremIdsForSelection selection = selection.previewPromotionTransitionIds := by
  simp [previewPromotionTheoremIdsForSelection, hCertified, hReady]

/-- Sprint obligation `HV.Package.PreviewPromotionTheoremIdsForSelectionWhenNotCertified`. -/
theorem previewPromotionTheoremIdsForSelectionWhenNotCertified
    (selection : Route.Selection)
    (hCertified : selection.record.previewPromotionCertified = false) :
    previewPromotionTheoremIdsForSelection selection = [] := by
  simp [previewPromotionTheoremIdsForSelection, hCertified]

/-- Sprint obligation `HV.Package.TheoremIdSelectionLength`. -/
theorem theoremIdSelectionLength
    (selection : Route.Selection) :
    (theoremIdsForSelection selection).length
      = (theoremIdsForRoute selection.record).length
        + (previewPromotionTheoremIdsForSelection selection).length := by
  simp [theoremIdsForSelection]

/-- Sprint obligation `HV.Package.TheoremIdsForSelectionWhenCertifiedReady`. -/
theorem theoremIdsForSelectionWhenCertifiedReady
    (selection : Route.Selection)
    (hCertified : selection.record.previewPromotionCertified = true)
    (hReady : selection.previewPromotionTransitionReady = true) :
    theoremIdsForSelection selection
      = theoremIdsForRoute selection.record ++ selection.previewPromotionTransitionIds := by
  simp [theoremIdsForSelection, previewPromotionTheoremIdsForSelection, hCertified, hReady]

/-- Sprint obligation `HV.Package.TheoremIdsForSelectionWhenNotCertified`. -/
theorem theoremIdsForSelectionWhenNotCertified
    (selection : Route.Selection)
    (hCertified : selection.record.previewPromotionCertified = false) :
    theoremIdsForSelection selection = theoremIdsForRoute selection.record := by
  simp [theoremIdsForSelection, previewPromotionTheoremIdsForSelection, hCertified]

/-- Sprint obligation `HV.Package.TheoremIdsForSelectionLengthWhenCertifiedReady`. -/
theorem theoremIdsForSelectionLengthWhenCertifiedReady
    (selection : Route.Selection)
    (hCertified : selection.record.previewPromotionCertified = true)
    (hReady : selection.previewPromotionTransitionReady = true) :
    (theoremIdsForSelection selection).length
      = (theoremIdsForRoute selection.record).length
        + selection.previewPromotionTransitionIds.length := by
  simp [theoremIdsForSelection, previewPromotionTheoremIdsForSelection, hCertified, hReady]

/-- Sprint obligation `HV.Package.TheoremIdsForSelectionLengthWhenNotCertified`. -/
theorem theoremIdsForSelectionLengthWhenNotCertified
    (selection : Route.Selection)
    (hCertified : selection.record.previewPromotionCertified = false) :
    (theoremIdsForSelection selection).length = (theoremIdsForRoute selection.record).length := by
  simp [theoremIdsForSelection, previewPromotionTheoremIdsForSelection, hCertified]

/-- Sprint obligation `HV.Package.TheoremContractIdsLength`. -/
theorem theoremContractIdsLength :
    theoremContractIds.length = 4 := by
  simp [theoremContractIds]

/-- Sprint obligation `HV.Package.TheoremContractIdsForVersionV1`. -/
theorem theoremContractIdsForVersionV1 :
    theoremContractIdsForVersion "v1" = theoremContractIds := by
  simp [theoremContractIdsForVersion]

/-- Sprint obligation `HV.Package.TheoremContractIdsForVersionCurrent`. -/
theorem theoremContractIdsForVersionCurrent :
    theoremContractIdsForVersion Route.promotionContractMetadataCurrentVersion = theoremContractIds := by
  simpa [Route.promotionContractMetadataCurrentVersion] using theoremContractIdsForVersionV1

/-- Sprint obligation `HV.Package.TheoremContractIdsForVersionV2Length`. -/
theorem theoremContractIdsForVersionV2Length :
    (theoremContractIdsForVersion "v2").length = 6 := by
  simp [theoremContractIdsForVersion, theoremContractIds, theoremContractV2ProjectionGuardIds]

/-- Sprint obligation `HV.Package.SharedTheoremContractIdsWithPolicyForVersionV1`. -/
theorem sharedTheoremContractIdsWithPolicyForVersionV1 (classId : String) :
    sharedTheoremContractIdsWithPolicyForVersion "v1" classId = sharedTheoremContractIdsWithPolicy classId := by
  simp [sharedTheoremContractIdsWithPolicyForVersion, sharedTheoremContractIdsWithPolicy,
    Route.promotionTransitionTheoremContractIdsForVersionV1, theoremContractIdsForVersion]

/-- Sprint obligation `HV.Package.TheoremContractIdsHasSelectionLink`. -/
theorem theoremContractIdsHasSelectionLink :
    "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenCertifiedReady"
      ∈ theoremContractIds := by
  simp [theoremContractIds]

/-- Sprint obligation `HV.Package.SharedTheoremContractIdsWithPolicyNonempty`. -/
theorem sharedTheoremContractIdsWithPolicyNonempty (classId : String) :
    (sharedTheoremContractIdsWithPolicy classId).isEmpty = false := by
  simp [sharedTheoremContractIdsWithPolicy, Route.promotionTransitionTheoremContractIds,
    Route.promotionTransitionBaseTheoremContractIds,
    Route.plannedRolloutWitnessPolicyContractIdsForRouteClass, theoremContractIds]

/-- Sprint obligation `HV.Package.SharedTheoremContractIdsWithPolicySelectionSingleton`. -/
theorem sharedTheoremContractIdsWithPolicySelectionSingleton (classId : String) :
    sharedTheoremContractIdsWithPolicy classId =
      ["HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenCertifiedReady"] := by
  by_cases hCpp : classId = "lambdair_highir_cpp"
  · subst hCpp
    simp [sharedTheoremContractIdsWithPolicy, Route.promotionTransitionTheoremContractIds,
      Route.promotionTransitionBaseTheoremContractIds,
      Route.plannedDerivationEndpointContractIdsForRouteClass,
      Route.plannedRolloutWitnessPolicyContractIdsForRouteClass, theoremContractIds]
  · by_cases hRust : classId = "lambdair_highir_rust"
    · subst hRust
      simp [sharedTheoremContractIdsWithPolicy, Route.promotionTransitionTheoremContractIds,
        Route.promotionTransitionBaseTheoremContractIds,
        Route.plannedDerivationEndpointContractIdsForRouteClass,
        Route.plannedRolloutWitnessPolicyContractIdsForRouteClass, theoremContractIds]
    · simp [sharedTheoremContractIdsWithPolicy, Route.promotionTransitionTheoremContractIds,
        Route.promotionTransitionBaseTheoremContractIds,
        Route.plannedDerivationEndpointContractIdsForRouteClass,
        Route.plannedRolloutWitnessPolicyContractIdsForRouteClass, theoremContractIds, hCpp, hRust]

/-- Sprint obligation `HV.Package.SharedTheoremContractIdsWithPolicyLength`. -/
theorem sharedTheoremContractIdsWithPolicyLength (classId : String) :
    (sharedTheoremContractIdsWithPolicy classId).length = 1 := by
  simp [sharedTheoremContractIdsWithPolicySelectionSingleton]

/-- Sprint obligation `HV.Package.SharedTheoremContractIdsWithPolicyHasSelectionLink`. -/
theorem sharedTheoremContractIdsWithPolicyHasSelectionLink (classId : String) :
    "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenCertifiedReady"
      ∈ sharedTheoremContractIdsWithPolicy classId := by
  simp [sharedTheoremContractIdsWithPolicy, Route.promotionTransitionTheoremContractIds,
    Route.promotionTransitionBaseTheoremContractIds,
    Route.plannedRolloutWitnessPolicyContractIdsForRouteClass, theoremContractIds]

/-- Sprint obligation `HV.Package.TheoremIdEnvelopeMatchesRouteTierPolicy`. -/
theorem theoremIdEnvelopeMatchesRouteTierPolicy
    (r : Route.RouteRecord)
    (hPolicy : r.preservationWitnessIds = Route.witnessIdsFor r.route r.witnessTier) :
    theoremIdsForRoute r = theoremIdsForRouteTier r.route r.witnessTier := by
  simp [theoremIdsForRoute, theoremIdsForRouteTier, hPolicy]

/-- Sprint obligation `HV.Package.SelectedTheoremEnvelopeMatchesProfilePolicy`. -/
theorem selectedTheoremEnvelopeMatchesProfilePolicy
    (m : DSL.Module)
    (route : Route.BackendRoute)
    (hHint : Route.parseBackendHint m.backendHint = some route)
    (hCompat : Route.routeSupportsTarget route m.backendTarget = true) :
    theoremIdsForRoute (Route.select m).record
      = theoremIdsForRouteTier route (Route.witnessTierForProfile m.packageProfile) := by
  have hWitness :=
    Route.selectedWitnessIdsForCompatibleRoute m route hHint hCompat
  simp [theoremIdsForRoute, theoremIdsForRouteTier, hWitness]

/-- Sprint obligation `HV.Package.SelectedTheoremEnvelopeBaseOnlyForIncompatibleRoute`. -/
theorem selectedTheoremEnvelopeBaseOnlyForIncompatibleRoute
    (m : DSL.Module)
    (route : Route.BackendRoute)
    (hHint : Route.parseBackendHint m.backendHint = some route)
    (hCompat : Route.routeSupportsTarget route m.backendTarget = false) :
    theoremIdsForRoute (Route.select m).record = baseTheoremIds := by
  have hWitness :=
    Route.selectedWitnessIdsEmptyForIncompatibleRoute m route hHint hCompat
  simp [theoremIdsForRoute, hWitness]

/-- Sprint obligation `HV.Package.MiniCOnlyDevTheoremEnvelopeLength`. -/
theorem miniCOnlyDevTheoremEnvelopeLength :
    (theoremIdsForRouteProfile .miniCOnly "dev").length = baseTheoremIds.length + 2 := by
  simp [theoremIdsForRouteProfile, theoremIdsForRouteTier, Route.witnessTierForProfile, Route.witnessIdsFor]

/-- Sprint obligation `HV.Package.MiniCOnlyProdStrictTheoremEnvelopeLength`. -/
theorem miniCOnlyProdStrictTheoremEnvelopeLength :
    (theoremIdsForRouteProfile .miniCOnly "prod_strict").length = baseTheoremIds.length + 5 := by
  simp [theoremIdsForRouteProfile, theoremIdsForRouteTier, Route.witnessTierForProfile, Route.witnessIdsFor]

end HeytingLean.HeytingVeil.Package
