import HeytingLean.HeytingVeil.Route.Policy
import HeytingLean.HeytingVeil.DSL.Syntax
import HeytingLean.HeytingVeil.Route.Witnesses
import HeytingLean.HeytingVeil.Route.ClassRegistry

namespace HeytingLean.HeytingVeil.Route

open HeytingLean.HeytingVeil

structure Selection where
  record : RouteRecord
  requestedHint : String
  requestedTarget : String
  targetClass : String
  rolloutStage : String
  derivationPlan : List String
  plannedPolicyTheoremIds : List String
  plannedEndpointRealizationTheoremIds : List String
  plannedBackendReadinessWitnessIds : List String
  plannedRolloutBridgeStrategy : String
  plannedRolloutBridgeWitnessIds : List String
  plannedRolloutBridgeReady : Bool
  plannedRolloutBridgeActionHooks : List String
  previewPromotionWitnessIds : List String
  previewSemanticsWitnessIds : List String
  previewPromotionReady : Bool
  previewPromotionVerdict : String
  previewPromotionReason : String
  previewPromotionTransitionIds : List String
  previewPromotionActionHooks : List String
  previewPromotionTransitionReady : Bool
  witnessTier : String
  hintRecognized : Bool
  routeImplemented : Bool
  targetCompatible : Bool
  routeClassSupportsTargetClass : Bool
  deriving Repr, DecidableEq

def parseBackendHint (hint : String) : Option BackendRoute :=
  match hint with
  | "lambdair_minic_c" => some .lambdaIRMiniCC
  | "lambdair_only" => some .lambdaIROnly
  | "minic_only" => some .miniCOnly
  | _ => none

def witnessTierForProfile (profile : String) : String :=
  if profile = "prod_strict" || profile = "extended" then "extended" else "minimal"

def witnessIdsFor (route : BackendRoute) (tier : String) : List String :=
  match route, tier with
  | .lambdaIRMiniCC, "extended" =>
      [ "HeytingLean.HeytingVeil.Route.Witnesses.lambdaIRToMiniCNatFrag"
      , "HeytingLean.HeytingVeil.Route.Witnesses.lambdaIRToMiniCNat2Frag"
      , "HeytingLean.HeytingVeil.Route.Witnesses.miniCToCRunNatFrag"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCReturnBridge"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCNormalBridge"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCFailureBridge"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCHaltedBridge"
      ]
  | .lambdaIRMiniCC, _ =>
      [ "HeytingLean.HeytingVeil.Route.Witnesses.lambdaIRToMiniCNatFrag"
      , "HeytingLean.HeytingVeil.Route.Witnesses.miniCToCRunNatFrag"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCReturnBridge"
      ]
  | .lambdaIROnly, "extended" =>
      [ "HeytingLean.HeytingVeil.Route.Witnesses.lambdaIRToMiniCNatFrag"
      , "HeytingLean.HeytingVeil.Route.Witnesses.lambdaIRToMiniCNat2Frag"
      ]
  | .lambdaIROnly, _ =>
      [ "HeytingLean.HeytingVeil.Route.Witnesses.lambdaIRToMiniCNatFrag"
      ]
  | .miniCOnly, "extended" =>
      [ "HeytingLean.HeytingVeil.Route.Witnesses.miniCToCRunNatFrag"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCReturnBridge"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCNormalBridge"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCFailureBridge"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCHaltedBridge"
      ]
  | .miniCOnly, _ =>
      [ "HeytingLean.HeytingVeil.Route.Witnesses.miniCToCRunNatFrag"
      , "HeytingLean.HeytingVeil.Route.Witnesses.heytingVeilMiniCReturnBridge"
      ]

def routeSupportsTarget (route : BackendRoute) (target : String) : Bool :=
  match route with
  | .lambdaIRMiniCC => target = "c"
  | .lambdaIROnly => target = "lambdair"
  | .miniCOnly => target = "minic" || target = "c"

def previewPromotionReadyFromMetadata
    (classId : String)
    (implemented compatible : Bool)
    (promotionWitnesses semanticsWitnesses : List String) : Bool :=
  implemented
    && compatible
    && isPreviewRouteClass classId
    && (!promotionWitnesses.isEmpty)
    && (!semanticsWitnesses.isEmpty)

def previewPromotionGateFromMetadata
    (classId : String)
    (implemented compatible ready : Bool)
    (plannedPolicyTheorems promotionWitnesses semanticsWitnesses : List String) : String × String :=
  if !isPreviewRouteClass classId then
    ("not_applicable", "not_preview_class")
  else if !implemented then
    ("blocked", "preview_not_implemented")
  else if !compatible then
    ("blocked", "target_incompatible")
  else if promotionWitnesses.isEmpty then
    ("blocked", "missing_preview_promotion_witnesses")
  else if semanticsWitnesses.isEmpty then
    ("blocked", "missing_preview_semantics_witnesses")
  else if plannedPolicyTheorems.isEmpty then
    ("blocked", "missing_preview_policy_theorems")
  else if ready then
    ("eligible", "ready_for_promotion")
  else
    ("blocked", "readiness_mismatch")

def previewPromotionTransitionIdsFromGate
    (classId verdict : String) : List String :=
  if verdict = "eligible" then
    previewPromotionTransitionIdsForRouteClass classId
  else
    []

def previewPromotionActionHooksFromGate
    (classId verdict reason : String) : List String :=
  if verdict = "eligible" then
    [s!"heytingveil package --promote-preview-route {classId}"
    ,s!"heytingveil verify --promotion-gate {reason}"
    ]
  else
    []

def previewPromotionTransitionReadyFromGate
    (transitionIds actionHooks : List String) : Bool :=
  (!transitionIds.isEmpty) && (!actionHooks.isEmpty)

def previewPromotionCertifiedFromMetadata
    (promoteRequested : Bool)
    (classId : String)
    (transitionReady : Bool) : Bool :=
  promoteRequested && isPreviewRouteClass classId && transitionReady

def promotionTransitionBaseTheoremContractIds : List String :=
  [ "HeytingLean.HeytingVeil.Route.selectedPreviewPromotionTransitionIdsMatchGatePolicy"
  , "HeytingLean.HeytingVeil.Route.selectedPreviewPromotionTransitionReadyMatchesGatePolicy"
  , "HeytingLean.HeytingVeil.Route.previewPromotionGateEligibleImpliesTransitionReady"
  , "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenCertifiedReady"
  , "HeytingLean.HeytingVeil.Route.selectedPlannedPolicyTheoremIdsMatchClassPolicy"
  , "HeytingLean.HeytingVeil.Route.plannedRouteClassNotImplementedFromFlag"
  , "HeytingLean.HeytingVeil.Route.plannedRouteClassDerivationContainsHighIR"
  ]

def plannedDerivationEndpointContractIdsForRouteClass (classId : String) : List String :=
  if classId = "lambdair_highir_cpp" then
    [ "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationEndsInCPP"
    ]
  else if classId = "lambdair_highir_rust" then
    [ "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationEndsInRust"
    ]
  else
    []

def plannedRolloutWitnessPolicyContractIdsForRouteClass (classId : String) : List String :=
  if classId = "lambdair_highir_cpp" then
    [ "HeytingLean.HeytingVeil.Route.backendFamilyRolloutWitnessIdsForRouteClassPlannedCpp"
    , "HeytingLean.HeytingVeil.Package.plannedRouteDowngradesUnverified"
    ]
  else if classId = "lambdair_highir_rust" then
    [ "HeytingLean.HeytingVeil.Route.backendFamilyRolloutWitnessIdsForRouteClassPlannedRust"
    , "HeytingLean.HeytingVeil.Package.plannedRouteDowngradesUnverified"
    ]
  else
    []

def endpointRuntimeReceiptContractIds : List String :=
  [ "HeytingLean.HeytingVeil.CLI.realizedEndpointRealizationReceiptWithOutcomes"
  , "HeytingLean.HeytingVeil.CLI.endpointRuntimeReceiptStatusGate"
  , "HeytingLean.HeytingVeil.CLI.endpointRuntimeReceiptStateCountDecomposition"
  ]

def endpointRuntimeReceiptContractIdsForVersion (_version : String) : List String :=
  endpointRuntimeReceiptContractIds

/-- Sprint obligation `HV.Route.EndpointRuntimeReceiptContractIdsLength`. -/
theorem endpointRuntimeReceiptContractIdsLength :
    endpointRuntimeReceiptContractIds.length = 3 := by
  simp [endpointRuntimeReceiptContractIds]

/-- Sprint obligation `HV.Route.EndpointRuntimeReceiptContractIdsForVersionV1`. -/
theorem endpointRuntimeReceiptContractIdsForVersionV1 :
    endpointRuntimeReceiptContractIdsForVersion "v1" = endpointRuntimeReceiptContractIds := by
  simp [endpointRuntimeReceiptContractIdsForVersion]

def promotionTransitionTheoremContractIds (classId : String) : List String :=
  promotionTransitionBaseTheoremContractIds ++
    plannedDerivationEndpointContractIdsForRouteClass classId ++
    plannedRolloutWitnessPolicyContractIdsForRouteClass classId

def promotionContractMetadataCurrentVersion : String := "v1"

def promotionContractMetadataSupportedVersions : List String := ["v1", "v2"]

/-- Sprint obligation `HV.Route.EndpointRuntimeReceiptContractIdsForVersionCurrent`. -/
theorem endpointRuntimeReceiptContractIdsForVersionCurrent :
    endpointRuntimeReceiptContractIdsForVersion promotionContractMetadataCurrentVersion
      = endpointRuntimeReceiptContractIds := by
  simp [endpointRuntimeReceiptContractIdsForVersion]

def resolvePromotionContractMetadataVersion (requested : String) : String :=
  if requested ∈ promotionContractMetadataSupportedVersions then
    requested
  else
    promotionContractMetadataCurrentVersion

/-- Sprint obligation `HV.Route.ResolvePromotionContractMetadataVersionSupported`. -/
theorem resolvePromotionContractMetadataVersionSupported (requested : String)
    (h : requested ∈ promotionContractMetadataSupportedVersions) :
    resolvePromotionContractMetadataVersion requested = requested := by
  simp [resolvePromotionContractMetadataVersion, h]

/-- Sprint obligation `HV.Route.ResolvePromotionContractMetadataVersionUnsupported`. -/
theorem resolvePromotionContractMetadataVersionUnsupported (requested : String)
    (h : requested ∉ promotionContractMetadataSupportedVersions) :
    resolvePromotionContractMetadataVersion requested = promotionContractMetadataCurrentVersion := by
  simp [resolvePromotionContractMetadataVersion, h]

/-- Sprint obligation `HV.Route.ResolvePromotionContractMetadataVersionCurrent`. -/
theorem resolvePromotionContractMetadataVersionCurrent :
    resolvePromotionContractMetadataVersion promotionContractMetadataCurrentVersion
      = promotionContractMetadataCurrentVersion := by
  simp [resolvePromotionContractMetadataVersion, promotionContractMetadataCurrentVersion,
    promotionContractMetadataSupportedVersions]

def promotionTransitionV2ProjectionGuardTheoremIds : List String :=
  [ "HeytingLean.HeytingVeil.Route.promotionTransitionTheoremContractIdsLengthPreviewHighIRC"
  , "HeytingLean.HeytingVeil.Package.sharedTheoremContractIdsWithPolicyLength"
  ]

def promotionTransitionTheoremContractIdsForVersion (version classId : String) : List String :=
  if version = "v2" then
    promotionTransitionTheoremContractIds classId ++ promotionTransitionV2ProjectionGuardTheoremIds
  else
    promotionTransitionTheoremContractIds classId

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsForVersionV1`. -/
theorem promotionTransitionTheoremContractIdsForVersionV1 (classId : String) :
    promotionTransitionTheoremContractIdsForVersion "v1" classId
      = promotionTransitionTheoremContractIds classId := by
  simp [promotionTransitionTheoremContractIdsForVersion]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsForVersionCurrent`. -/
theorem promotionTransitionTheoremContractIdsForVersionCurrent (classId : String) :
    promotionTransitionTheoremContractIdsForVersion promotionContractMetadataCurrentVersion classId
      = promotionTransitionTheoremContractIds classId := by
  simpa [promotionContractMetadataCurrentVersion] using
    promotionTransitionTheoremContractIdsForVersionV1 classId

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsForVersionV2LengthStable`. -/
theorem promotionTransitionTheoremContractIdsForVersionV2LengthStable (route : BackendRoute) :
    (promotionTransitionTheoremContractIdsForVersion "v2" (routeClassIdFor route)).length = 9 := by
  cases route <;>
    simp [promotionTransitionTheoremContractIdsForVersion, promotionTransitionV2ProjectionGuardTheoremIds,
      promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
      plannedDerivationEndpointContractIdsForRouteClass,
      plannedRolloutWitnessPolicyContractIdsForRouteClass, routeClassIdFor]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsForVersionV2LengthPlannedCpp`. -/
theorem promotionTransitionTheoremContractIdsForVersionV2LengthPlannedCpp :
    (promotionTransitionTheoremContractIdsForVersion "v2" "lambdair_highir_cpp").length = 13 := by
  simp [promotionTransitionTheoremContractIdsForVersion, promotionTransitionV2ProjectionGuardTheoremIds,
    promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
    plannedDerivationEndpointContractIdsForRouteClass,
    plannedRolloutWitnessPolicyContractIdsForRouteClass]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsForVersionV2LengthPlannedRust`. -/
theorem promotionTransitionTheoremContractIdsForVersionV2LengthPlannedRust :
    (promotionTransitionTheoremContractIdsForVersion "v2" "lambdair_highir_rust").length = 13 := by
  simp [promotionTransitionTheoremContractIdsForVersion, promotionTransitionV2ProjectionGuardTheoremIds,
    promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
    plannedDerivationEndpointContractIdsForRouteClass,
    plannedRolloutWitnessPolicyContractIdsForRouteClass]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsLength`. -/
theorem promotionTransitionTheoremContractIdsLength :
    promotionTransitionBaseTheoremContractIds.length = 7 := by
  simp [promotionTransitionBaseTheoremContractIds]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsLengthStable`. -/
theorem promotionTransitionTheoremContractIdsLengthStable (route : BackendRoute) :
    (promotionTransitionTheoremContractIds (routeClassIdFor route)).length = 7 := by
  cases route <;>
    simp [promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
      plannedDerivationEndpointContractIdsForRouteClass,
      plannedRolloutWitnessPolicyContractIdsForRouteClass, routeClassIdFor]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsLengthPlannedCpp`. -/
theorem promotionTransitionTheoremContractIdsLengthPlannedCpp :
    (promotionTransitionTheoremContractIds "lambdair_highir_cpp").length = 11 := by
  simp [promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
    plannedDerivationEndpointContractIdsForRouteClass,
    plannedRolloutWitnessPolicyContractIdsForRouteClass]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsLengthPlannedRust`. -/
theorem promotionTransitionTheoremContractIdsLengthPlannedRust :
    (promotionTransitionTheoremContractIds "lambdair_highir_rust").length = 11 := by
  simp [promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
    plannedDerivationEndpointContractIdsForRouteClass,
    plannedRolloutWitnessPolicyContractIdsForRouteClass]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsLengthNonPlanned`. -/
theorem promotionTransitionTheoremContractIdsLengthNonPlanned
    (classId : String)
    (hCpp : classId ≠ "lambdair_highir_cpp")
    (hRust : classId ≠ "lambdair_highir_rust") :
    (promotionTransitionTheoremContractIds classId).length = 7 := by
  simp [promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
    plannedDerivationEndpointContractIdsForRouteClass,
    plannedRolloutWitnessPolicyContractIdsForRouteClass, hCpp, hRust]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsLengthPreviewHighIRC`. -/
theorem promotionTransitionTheoremContractIdsLengthPreviewHighIRC :
    (promotionTransitionTheoremContractIds "lambdair_highir_c").length = 7 := by
  exact promotionTransitionTheoremContractIdsLengthNonPlanned "lambdair_highir_c"
    (by decide) (by decide)

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsHasPlannedPolicyLink`. -/
theorem promotionTransitionTheoremContractIdsHasPlannedPolicyLink (classId : String) :
    "HeytingLean.HeytingVeil.Route.selectedPlannedPolicyTheoremIdsMatchClassPolicy"
      ∈ promotionTransitionTheoremContractIds classId := by
  simp [promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsHasPackageSelectionLink`. -/
theorem promotionTransitionTheoremContractIdsHasPackageSelectionLink (classId : String) :
    "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenCertifiedReady"
      ∈ promotionTransitionTheoremContractIds classId := by
  simp [promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsHasRolloutWitnessLinkPlannedCpp`. -/
theorem promotionTransitionTheoremContractIdsHasRolloutWitnessLinkPlannedCpp :
    (backendFamilyRolloutWitnessTheoremIdsForRouteClass "lambdair_highir_cpp").all
      (promotionTransitionTheoremContractIds "lambdair_highir_cpp").contains = true := by
  simp [promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
    plannedDerivationEndpointContractIdsForRouteClass,
    plannedRolloutWitnessPolicyContractIdsForRouteClass,
    backendFamilyRolloutWitnessTheoremIdsForRouteClass,
    backendFamilyRolloutReasonForRouteClass, backendFamilyRolloutWitnessTheoremIdsForReason,
    isPlannedRouteClass, plannedRouteClassIds]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsHasRolloutWitnessLinkPlannedRust`. -/
theorem promotionTransitionTheoremContractIdsHasRolloutWitnessLinkPlannedRust :
    (backendFamilyRolloutWitnessTheoremIdsForRouteClass "lambdair_highir_rust").all
      (promotionTransitionTheoremContractIds "lambdair_highir_rust").contains = true := by
  simp [promotionTransitionTheoremContractIds, promotionTransitionBaseTheoremContractIds,
    plannedDerivationEndpointContractIdsForRouteClass,
    plannedRolloutWitnessPolicyContractIdsForRouteClass,
    backendFamilyRolloutWitnessTheoremIdsForRouteClass,
    backendFamilyRolloutReasonForRouteClass, backendFamilyRolloutWitnessTheoremIdsForReason,
    isPlannedRouteClass, plannedRouteClassIds]

/-- Sprint obligation `HV.Route.PromotionTransitionTheoremContractIdsHasRolloutWitnessLinkStableRoutes`. -/
theorem promotionTransitionTheoremContractIdsHasRolloutWitnessLinkStableRoutes (route : BackendRoute) :
    (backendFamilyRolloutWitnessTheoremIdsForRouteClass (routeClassIdFor route)).all
      (promotionTransitionTheoremContractIds (routeClassIdFor route)).contains = true := by
  have hEmpty :
      backendFamilyRolloutWitnessTheoremIdsForRouteClass (routeClassIdFor route) = [] :=
    backendFamilyRolloutWitnessIdsForImplementedStableRoutes route
  rw [hEmpty]
  simp

/-- Sprint obligation `HV.Route.PreviewPromotionCertifiedFromMetadataPolicy`. -/
theorem previewPromotionCertifiedFromMetadataPolicy
    (promoteRequested : Bool)
    (classId : String)
    (transitionReady : Bool) :
    previewPromotionCertifiedFromMetadata promoteRequested classId transitionReady
      = (promoteRequested && isPreviewRouteClass classId && transitionReady) := by
  rfl

/-- Sprint obligation `HV.Route.PreviewPromotionCertifiedFromMetadataEqTrueIff`. -/
theorem previewPromotionCertifiedFromMetadataEqTrueIff
    (promoteRequested : Bool)
    (classId : String)
    (transitionReady : Bool) :
    previewPromotionCertifiedFromMetadata promoteRequested classId transitionReady = true
      ↔ promoteRequested = true
        ∧ isPreviewRouteClass classId = true
        ∧ transitionReady = true := by
  constructor
  · intro h
    have h' :
        (promoteRequested = true ∧ isPreviewRouteClass classId = true)
          ∧ transitionReady = true := by
      simpa [previewPromotionCertifiedFromMetadata, Bool.and_eq_true] using h
    exact ⟨h'.1.1, h'.1.2, h'.2⟩
  · intro h
    have h' :
        (promoteRequested = true ∧ isPreviewRouteClass classId = true)
          ∧ transitionReady = true :=
      ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    simpa [previewPromotionCertifiedFromMetadata, Bool.and_eq_true] using h'

/-- Sprint obligation `HV.Route.RouteClassSupportMatchesRoutePolicy`. -/
theorem routeClassSupportMatchesRoutePolicy
    (route : BackendRoute) (target : String) :
    supportsTargetClass (routeClassIdFor route) (targetClassForTarget target)
      = routeSupportsTarget route target := by
  cases route with
  | lambdaIRMiniCC =>
      by_cases hc : target = "c" <;>
        by_cases hcpp : target = "cpp" <;>
        by_cases hrust : target = "rust" <;>
        by_cases hlir : target = "lambdair" <;>
        by_cases hminic : target = "minic" <;>
        simp [routeSupportsTarget, routeClassIdFor, supportsTargetClass, targetClassForTarget,
          hc, hcpp, hrust, hlir, hminic]
  | lambdaIROnly =>
      by_cases hc : target = "c" <;>
        by_cases hcpp : target = "cpp" <;>
        by_cases hrust : target = "rust" <;>
        by_cases hlir : target = "lambdair" <;>
        by_cases hminic : target = "minic" <;>
        simp [routeSupportsTarget, routeClassIdFor, supportsTargetClass, targetClassForTarget,
          hc, hcpp, hrust, hlir, hminic]
  | miniCOnly =>
      by_cases hc : target = "c" <;>
        by_cases hcpp : target = "cpp" <;>
        by_cases hrust : target = "rust" <;>
        by_cases hlir : target = "lambdair" <;>
        by_cases hminic : target = "minic" <;>
        simp [routeSupportsTarget, routeClassIdFor, supportsTargetClass, targetClassForTarget,
          hc, hcpp, hrust, hlir, hminic]

private def certificateRequested (m : DSL.Module) : Bool :=
  m.packageCertificate = "cab_export_v2"

/--
Select route from parsed DSL metadata. Unknown hints and incompatible targets
are preserved as explicit diagnostics and downgraded to unproven routing.
-/
def select (m : DSL.Module) : Selection :=
  let tier := witnessTierForProfile m.packageProfile
  let targetClass := targetClassForTarget m.backendTarget
  match parseBackendHint m.backendHint with
  | none =>
      let recognized := isKnownRouteClass m.backendHint
      let classId := if recognized then m.backendHint else "unknown"
      let implemented := isImplementedRouteClass classId
      let stage := rolloutStageForRouteClass classId
      let derivationPlan := derivationPlanForRouteClass classId
      let plannedPolicyTheoremIds := plannedPolicyTheoremIdsForRouteClass classId
      let plannedEndpointRealizationTheoremIds :=
        plannedEndpointRealizationTheoremIdsForRouteClass classId
      let plannedBackendReadinessWitnessIds :=
        plannedBackendReadinessWitnessIdsForRouteClass classId
      let plannedRolloutBridgeStrategy := plannedRolloutBridgeStrategyForRouteClass classId
      let plannedRolloutBridgeWitnessIds := plannedRolloutBridgeWitnessIdsForRouteClass classId
      let plannedRolloutBridgeReady := plannedRolloutBridgeReadyForRouteClass classId
      let plannedRolloutBridgeActionHooks := plannedRolloutBridgeActionHooksForRouteClass classId
      let previewPromotionWitnessIds := previewPromotionWitnessIdsForRouteClass classId
      let previewSemanticsWitnessIds := previewSemanticsWitnessIdsForRouteClass classId
      let classSupports := supportsTargetClass classId targetClass
      let previewPromotionReady := previewPromotionReadyFromMetadata
        classId implemented classSupports previewPromotionWitnessIds previewSemanticsWitnessIds
      let (previewPromotionVerdict, previewPromotionReason) := previewPromotionGateFromMetadata
        classId
        implemented
        classSupports
        previewPromotionReady
        plannedPolicyTheoremIds
        previewPromotionWitnessIds
        previewSemanticsWitnessIds
      let previewPromotionTransitionIds := previewPromotionTransitionIdsFromGate
        classId previewPromotionVerdict
      let previewPromotionActionHooks := previewPromotionActionHooksFromGate
        classId previewPromotionVerdict previewPromotionReason
      let previewPromotionTransitionReady := previewPromotionTransitionReadyFromGate
        previewPromotionTransitionIds previewPromotionActionHooks
      { record :=
          { route := .lambdaIRMiniCC
            routeClassId := classId
            preservationWitnessIds := []
            previewPromotionReady := previewPromotionReady
            witnessTier := tier
            certifiedRequested := certificateRequested m }
        requestedHint := m.backendHint
        requestedTarget := m.backendTarget
        targetClass := targetClass
        rolloutStage := stage
        derivationPlan := derivationPlan
        plannedPolicyTheoremIds := plannedPolicyTheoremIds
        plannedEndpointRealizationTheoremIds := plannedEndpointRealizationTheoremIds
        plannedBackendReadinessWitnessIds := plannedBackendReadinessWitnessIds
        plannedRolloutBridgeStrategy := plannedRolloutBridgeStrategy
        plannedRolloutBridgeWitnessIds := plannedRolloutBridgeWitnessIds
        plannedRolloutBridgeReady := plannedRolloutBridgeReady
        plannedRolloutBridgeActionHooks := plannedRolloutBridgeActionHooks
        previewPromotionWitnessIds := previewPromotionWitnessIds
        previewSemanticsWitnessIds := previewSemanticsWitnessIds
        previewPromotionReady := previewPromotionReady
        previewPromotionVerdict := previewPromotionVerdict
        previewPromotionReason := previewPromotionReason
        previewPromotionTransitionIds := previewPromotionTransitionIds
        previewPromotionActionHooks := previewPromotionActionHooks
        previewPromotionTransitionReady := previewPromotionTransitionReady
        witnessTier := tier
        hintRecognized := recognized
        routeImplemented := implemented
        targetCompatible := classSupports
        routeClassSupportsTargetClass := classSupports }
  | some route =>
      let compatible := routeSupportsTarget route m.backendTarget
      let classId := routeClassIdFor route
      let implemented := isImplementedRouteClass classId
      let stage := rolloutStageForRouteClass classId
      let derivationPlan := derivationPlanForRouteClass classId
      let plannedPolicyTheoremIds := plannedPolicyTheoremIdsForRouteClass classId
      let plannedEndpointRealizationTheoremIds :=
        plannedEndpointRealizationTheoremIdsForRouteClass classId
      let plannedBackendReadinessWitnessIds :=
        plannedBackendReadinessWitnessIdsForRouteClass classId
      let plannedRolloutBridgeStrategy := plannedRolloutBridgeStrategyForRouteClass classId
      let plannedRolloutBridgeWitnessIds := plannedRolloutBridgeWitnessIdsForRouteClass classId
      let plannedRolloutBridgeReady := plannedRolloutBridgeReadyForRouteClass classId
      let plannedRolloutBridgeActionHooks := plannedRolloutBridgeActionHooksForRouteClass classId
      let previewPromotionWitnessIds := previewPromotionWitnessIdsForRouteClass classId
      let previewSemanticsWitnessIds := previewSemanticsWitnessIdsForRouteClass classId
      let classSupports := supportsTargetClass classId targetClass
      let witnessIds := if compatible then witnessIdsFor route tier else []
      let previewPromotionReady := previewPromotionReadyFromMetadata
        classId implemented compatible previewPromotionWitnessIds previewSemanticsWitnessIds
      let (previewPromotionVerdict, previewPromotionReason) := previewPromotionGateFromMetadata
        classId
        implemented
        compatible
        previewPromotionReady
        plannedPolicyTheoremIds
        previewPromotionWitnessIds
        previewSemanticsWitnessIds
      let previewPromotionTransitionIds := previewPromotionTransitionIdsFromGate
        classId previewPromotionVerdict
      let previewPromotionActionHooks := previewPromotionActionHooksFromGate
        classId previewPromotionVerdict previewPromotionReason
      let previewPromotionTransitionReady := previewPromotionTransitionReadyFromGate
        previewPromotionTransitionIds previewPromotionActionHooks
      { record :=
          { route := route
            routeClassId := classId
            preservationWitnessIds := witnessIds
            previewPromotionReady := previewPromotionReady
            witnessTier := tier
            certifiedRequested := certificateRequested m }
        requestedHint := m.backendHint
        requestedTarget := m.backendTarget
        targetClass := targetClass
        rolloutStage := stage
        derivationPlan := derivationPlan
        plannedPolicyTheoremIds := plannedPolicyTheoremIds
        plannedEndpointRealizationTheoremIds := plannedEndpointRealizationTheoremIds
        plannedBackendReadinessWitnessIds := plannedBackendReadinessWitnessIds
        plannedRolloutBridgeStrategy := plannedRolloutBridgeStrategy
        plannedRolloutBridgeWitnessIds := plannedRolloutBridgeWitnessIds
        plannedRolloutBridgeReady := plannedRolloutBridgeReady
        plannedRolloutBridgeActionHooks := plannedRolloutBridgeActionHooks
        previewPromotionWitnessIds := previewPromotionWitnessIds
        previewSemanticsWitnessIds := previewSemanticsWitnessIds
        previewPromotionReady := previewPromotionReady
        previewPromotionVerdict := previewPromotionVerdict
        previewPromotionReason := previewPromotionReason
        previewPromotionTransitionIds := previewPromotionTransitionIds
        previewPromotionActionHooks := previewPromotionActionHooks
        previewPromotionTransitionReady := previewPromotionTransitionReady
        witnessTier := tier
        hintRecognized := true
        routeImplemented := implemented
        targetCompatible := compatible
        routeClassSupportsTargetClass := classSupports }

/-- Sprint obligation `HV.Route.SelectionDeterministic`. -/
theorem selectionDeterministic (m : DSL.Module) :
    select m = select m := rfl

/-- Sprint obligation `HV.Route.CertRequestFromPackageCertificate`. -/
theorem certRequestFromPackageCertificate (m : DSL.Module) :
    (select m).record.certifiedRequested = (m.packageCertificate = "cab_export_v2") := by
  unfold select
  cases h : parseBackendHint m.backendHint <;> simp [certificateRequested]

/-- Sprint obligation `HV.Route.SelectedWitnessIdsForCompatibleRoute`. -/
theorem selectedWitnessIdsForCompatibleRoute
    (m : DSL.Module)
    (route : BackendRoute)
    (hHint : parseBackendHint m.backendHint = some route)
    (hCompat : routeSupportsTarget route m.backendTarget = true) :
    (select m).record.preservationWitnessIds
      = witnessIdsFor route (witnessTierForProfile m.packageProfile) := by
  unfold select
  simp [hHint, hCompat]

/-- Sprint obligation `HV.Route.SelectedWitnessIdsEmptyForIncompatibleRoute`. -/
theorem selectedWitnessIdsEmptyForIncompatibleRoute
    (m : DSL.Module)
    (route : BackendRoute)
    (hHint : parseBackendHint m.backendHint = some route)
    (hCompat : routeSupportsTarget route m.backendTarget = false) :
    (select m).record.preservationWitnessIds = [] := by
  unfold select
  simp [hHint, hCompat]

/-- Sprint obligation `HV.Route.WitnessIdsForNeverEmpty`. -/
theorem witnessIdsForNeverEmpty
    (route : BackendRoute)
    (tier : String) :
    (witnessIdsFor route tier).isEmpty = false := by
  cases route <;> by_cases hTier : tier = "extended" <;> simp [witnessIdsFor, hTier]

/-- Sprint obligation `HV.Route.SelectedCompatibleHasWitnesses`. -/
theorem selectedCompatibleHasWitnesses
    (m : DSL.Module)
    (route : BackendRoute)
    (hHint : parseBackendHint m.backendHint = some route)
    (hCompat : routeSupportsTarget route m.backendTarget = true) :
    ((select m).record.preservationWitnessIds).isEmpty = false := by
  rw [selectedWitnessIdsForCompatibleRoute m route hHint hCompat]
  exact witnessIdsForNeverEmpty route (witnessTierForProfile m.packageProfile)

/-- Sprint obligation `HV.Route.SelectedRecognizedRouteClassStable`. -/
theorem selectedRecognizedRouteClassStable
    (m : DSL.Module)
    (route : BackendRoute)
    (hHint : parseBackendHint m.backendHint = some route) :
    isStableRouteClass (select m).record.routeClassId = true := by
  have hStable : isStableRouteClass (routeClassIdFor route) = true :=
    routeClassIdForIsStable route
  unfold select
  simp [hHint, hStable]

/-- Sprint obligation `HV.Route.SelectedRouteImplementedMatchesClassPolicy`. -/
theorem selectedRouteImplementedMatchesClassPolicy (m : DSL.Module) :
    (select m).routeImplemented
      = isImplementedRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedRolloutStageMatchesClassPolicy`. -/
theorem selectedRolloutStageMatchesClassPolicy (m : DSL.Module) :
    (select m).rolloutStage
      = rolloutStageForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedDerivationPlanMatchesClassPolicy`. -/
theorem selectedDerivationPlanMatchesClassPolicy (m : DSL.Module) :
    (select m).derivationPlan
      = derivationPlanForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPlannedPolicyTheoremIdsMatchClassPolicy`. -/
theorem selectedPlannedPolicyTheoremIdsMatchClassPolicy (m : DSL.Module) :
    (select m).plannedPolicyTheoremIds
      = plannedPolicyTheoremIdsForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPlannedEndpointRealizationTheoremIdsMatchClassPolicy`. -/
theorem selectedPlannedEndpointRealizationTheoremIdsMatchClassPolicy (m : DSL.Module) :
    (select m).plannedEndpointRealizationTheoremIds
      = plannedEndpointRealizationTheoremIdsForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPlannedBackendReadinessWitnessIdsMatchClassPolicy`. -/
theorem selectedPlannedBackendReadinessWitnessIdsMatchClassPolicy (m : DSL.Module) :
    (select m).plannedBackendReadinessWitnessIds
      = plannedBackendReadinessWitnessIdsForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPlannedRolloutBridgeStrategyMatchesClassPolicy`. -/
theorem selectedPlannedRolloutBridgeStrategyMatchesClassPolicy (m : DSL.Module) :
    (select m).plannedRolloutBridgeStrategy
      = plannedRolloutBridgeStrategyForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPlannedRolloutBridgeWitnessIdsMatchClassPolicy`. -/
theorem selectedPlannedRolloutBridgeWitnessIdsMatchClassPolicy (m : DSL.Module) :
    (select m).plannedRolloutBridgeWitnessIds
      = plannedRolloutBridgeWitnessIdsForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPlannedRolloutBridgeReadyMatchesClassPolicy`. -/
theorem selectedPlannedRolloutBridgeReadyMatchesClassPolicy (m : DSL.Module) :
    (select m).plannedRolloutBridgeReady
      = plannedRolloutBridgeReadyForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPlannedRolloutBridgeActionHooksMatchClassPolicy`. -/
theorem selectedPlannedRolloutBridgeActionHooksMatchClassPolicy (m : DSL.Module) :
    (select m).plannedRolloutBridgeActionHooks
      = plannedRolloutBridgeActionHooksForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPreviewPromotionWitnessIdsMatchClassPolicy`. -/
theorem selectedPreviewPromotionWitnessIdsMatchClassPolicy (m : DSL.Module) :
    (select m).previewPromotionWitnessIds
      = previewPromotionWitnessIdsForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPreviewSemanticsWitnessIdsMatchClassPolicy`. -/
theorem selectedPreviewSemanticsWitnessIdsMatchClassPolicy (m : DSL.Module) :
    (select m).previewSemanticsWitnessIds
      = previewSemanticsWitnessIdsForRouteClass (select m).record.routeClassId := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp

/-- Sprint obligation `HV.Route.SelectedPreviewPromotionReadyMatchesMetadataPolicy`. -/
theorem selectedPreviewPromotionReadyMatchesMetadataPolicy (m : DSL.Module) :
    (select m).previewPromotionReady
      = previewPromotionReadyFromMetadata
          (select m).record.routeClassId
          (select m).routeImplemented
          (select m).targetCompatible
          (select m).previewPromotionWitnessIds
          (select m).previewSemanticsWitnessIds := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp [previewPromotionReadyFromMetadata]

/-- Sprint obligation `HV.Route.SelectedPreviewPromotionGateMatchesMetadataPolicy`. -/
theorem selectedPreviewPromotionGateMatchesMetadataPolicy (m : DSL.Module) :
    ((select m).previewPromotionVerdict, (select m).previewPromotionReason)
      = previewPromotionGateFromMetadata
          (select m).record.routeClassId
          (select m).routeImplemented
          (select m).targetCompatible
          (select m).previewPromotionReady
          (select m).plannedPolicyTheoremIds
          (select m).previewPromotionWitnessIds
          (select m).previewSemanticsWitnessIds := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp [previewPromotionGateFromMetadata]

/-- Sprint obligation `HV.Route.SelectedPreviewPromotionTransitionIdsMatchGatePolicy`. -/
theorem selectedPreviewPromotionTransitionIdsMatchGatePolicy (m : DSL.Module) :
    (select m).previewPromotionTransitionIds
      = previewPromotionTransitionIdsFromGate
          (select m).record.routeClassId
          (select m).previewPromotionVerdict := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp [previewPromotionTransitionIdsFromGate]

/-- Sprint obligation `HV.Route.SelectedPreviewPromotionActionHooksMatchGatePolicy`. -/
theorem selectedPreviewPromotionActionHooksMatchGatePolicy (m : DSL.Module) :
    (select m).previewPromotionActionHooks
      = previewPromotionActionHooksFromGate
          (select m).record.routeClassId
          (select m).previewPromotionVerdict
          (select m).previewPromotionReason := by
  unfold select
  cases parseBackendHint m.backendHint <;> simp [previewPromotionActionHooksFromGate]

/-- Sprint obligation `HV.Route.SelectedPreviewPromotionTransitionReadyMatchesGatePolicy`. -/
theorem selectedPreviewPromotionTransitionReadyMatchesGatePolicy (m : DSL.Module) :
    (select m).previewPromotionTransitionReady
      = previewPromotionTransitionReadyFromGate
          (select m).previewPromotionTransitionIds
          (select m).previewPromotionActionHooks := by
  unfold select
  cases parseBackendHint m.backendHint <;>
    simp [previewPromotionTransitionReadyFromGate, previewPromotionTransitionIdsFromGate,
      previewPromotionActionHooksFromGate]

/-- Sprint obligation `HV.Route.SelectedPreviewPromotionCertifiedMatchesGateMetadata`. -/
theorem selectedPreviewPromotionCertifiedMatchesGateMetadata
    (m : DSL.Module)
    (promoteRequested : Bool) :
    previewPromotionCertifiedFromMetadata
        promoteRequested
        (select m).record.routeClassId
        (select m).previewPromotionTransitionReady
      = (promoteRequested
          && isPreviewRouteClass (select m).record.routeClassId
          && previewPromotionTransitionReadyFromGate
              (select m).previewPromotionTransitionIds
              (select m).previewPromotionActionHooks) := by
  rw [selectedPreviewPromotionTransitionReadyMatchesGatePolicy]
  rfl

/-- Sprint obligation `HV.Route.PreviewPromotionGateEligibleImpliesTransitionReady`. -/
theorem previewPromotionGateEligibleImpliesTransitionReady (classId : String)
    (hPreview : isPreviewRouteClass classId = true) :
    previewPromotionTransitionReadyFromGate
        (previewPromotionTransitionIdsFromGate classId "eligible")
        (previewPromotionActionHooksFromGate classId "eligible" "ready_for_promotion")
      = true := by
  have hTransitions :
      (previewPromotionTransitionIdsForRouteClass classId).isEmpty = false := by
    exact previewPromotionTransitionIdsNonemptyForPreviewClass classId hPreview
  simp [previewPromotionTransitionReadyFromGate, previewPromotionTransitionIdsFromGate,
    previewPromotionActionHooksFromGate, hTransitions]

/-- Sprint obligation `HV.Route.SelectedRecognizedClassSupportMatchesCompatibility`. -/
theorem selectedRecognizedClassSupportMatchesCompatibility
    (m : DSL.Module)
    (route : BackendRoute)
    (hHint : parseBackendHint m.backendHint = some route) :
    (select m).routeClassSupportsTargetClass = (select m).targetCompatible := by
  unfold select
  simp [hHint, routeClassSupportMatchesRoutePolicy]

/-- Sprint obligation `HV.Route.SelectedPlannedHintRecognizedUnimplemented`. -/
theorem selectedPlannedHintRecognizedUnimplemented
    (m : DSL.Module)
    (hParse : parseBackendHint m.backendHint = none)
    (hPlanned : isPlannedRouteClass m.backendHint = true) :
    (select m).hintRecognized = true
      ∧ (select m).routeImplemented = false
      ∧ (select m).rolloutStage = "planned"
      ∧ (select m).record.routeClassId = m.backendHint
      ∧ "HighIR" ∈ (select m).derivationPlan
      ∧ ((select m).plannedPolicyTheoremIds).isEmpty = false := by
  unfold select
  have hNotImpl : isImplementedRouteClass m.backendHint = false := by
    exact plannedRouteClassNotImplementedFromFlag m.backendHint hPlanned
  have hKnown : isKnownRouteClass m.backendHint = true := by
    have hIn : m.backendHint ∈ plannedRouteClassIds := by
      simpa [isPlannedRouteClass] using hPlanned
    simp [isKnownRouteClass, knownRouteClassIds, hIn]
  have hHighIR : "HighIR" ∈ derivationPlanForRouteClass m.backendHint := by
    exact plannedRouteClassDerivationContainsHighIR m.backendHint hPlanned
  have hPlannedPolicy :
      (plannedPolicyTheoremIdsForRouteClass m.backendHint).isEmpty = false := by
    exact plannedPolicyTheoremIdsNonemptyForPlannedClass m.backendHint hPlanned
  have hPlannedIn : m.backendHint ∈ plannedRouteClassIds := by
    simpa [isPlannedRouteClass] using hPlanned
  have hCases :
      m.backendHint = "lambdair_highir_cpp"
      ∨ m.backendHint = "lambdair_highir_rust" := by
    simpa [plannedRouteClassIds] using hPlannedIn
  have hNotPreview : isPreviewRouteClass m.backendHint = false := by
    rcases hCases with hCpp | hRust
    · simp [isPreviewRouteClass, previewRouteClassIds, hCpp]
    · simp [isPreviewRouteClass, previewRouteClassIds, hRust]
  have hNotStable : isStableRouteClass m.backendHint = false := by
    rcases hCases with hCpp | hRust
    · simp [isStableRouteClass, stableRouteClassIds, hCpp]
    · simp [isStableRouteClass, stableRouteClassIds, hRust]
  simp [hParse, hPlanned, hKnown, hNotImpl, hNotPreview, hNotStable,
    rolloutStageForRouteClass, hHighIR, hPlannedPolicy]

/-- Sprint obligation `HV.Route.SelectedPreviewHintRecognizedImplemented`. -/
theorem selectedPreviewHintRecognizedImplemented
    (m : DSL.Module)
    (hParse : parseBackendHint m.backendHint = none)
    (hPreview : isPreviewRouteClass m.backendHint = true) :
    (select m).hintRecognized = true
      ∧ (select m).routeImplemented = true
      ∧ (select m).rolloutStage = "preview"
      ∧ (select m).record.routeClassId = m.backendHint
      ∧ "HighIR" ∈ (select m).derivationPlan
      ∧ ((select m).plannedPolicyTheoremIds).isEmpty = false
      ∧ ((select m).previewPromotionWitnessIds).isEmpty = false
      ∧ ((select m).previewSemanticsWitnessIds).isEmpty = false
      ∧ (select m).previewPromotionReady
          = (supportsTargetClass m.backendHint (targetClassForTarget m.backendTarget)) := by
  unfold select
  have hImpl : isImplementedRouteClass m.backendHint = true := by
    exact previewRouteClassImplementedFromFlag m.backendHint hPreview
  have hKnown : isKnownRouteClass m.backendHint = true := by
    have hIn : m.backendHint ∈ previewRouteClassIds := by
      simpa [isPreviewRouteClass] using hPreview
    simp [isKnownRouteClass, knownRouteClassIds, hIn]
  have hStage : rolloutStageForRouteClass m.backendHint = "preview" := by
    exact rolloutStagePreviewForPreviewRoute m.backendHint hPreview
  have hHighIR : "HighIR" ∈ derivationPlanForRouteClass m.backendHint := by
    exact previewRouteClassDerivationContainsHighIR m.backendHint hPreview
  have hPlannedPolicy :
      (plannedPolicyTheoremIdsForRouteClass m.backendHint).isEmpty = false := by
    exact plannedPolicyTheoremIdsNonemptyForPreviewClass m.backendHint hPreview
  have hPreviewPromotion :
      (previewPromotionWitnessIdsForRouteClass m.backendHint).isEmpty = false := by
    exact previewPromotionWitnessIdsNonemptyForPreviewClass m.backendHint hPreview
  have hPreviewSemantics :
      (previewSemanticsWitnessIdsForRouteClass m.backendHint).isEmpty = false := by
    exact previewSemanticsWitnessIdsNonemptyForPreviewClass m.backendHint hPreview
  simp [hParse, hKnown, hImpl, hStage, hHighIR, hPlannedPolicy, hPreviewPromotion,
    hPreviewSemantics, hPreview, previewPromotionReadyFromMetadata]

/-- Sprint obligation `HV.Route.RecordTierMatchesSelectionTier`. -/
theorem recordTierMatchesSelectionTier (m : DSL.Module) :
    (select m).record.witnessTier = (select m).witnessTier := by
  unfold select
  cases h : parseBackendHint m.backendHint <;> simp

end HeytingLean.HeytingVeil.Route
