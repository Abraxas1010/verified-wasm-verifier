import HeytingLean.HeytingVeil.Route.Record
import HeytingLean.HeytingVeil.HighIR.ToC
import HeytingLean.HeytingVeil.HighIR.ToCPP
import HeytingLean.HeytingVeil.HighIR.ToRust

namespace HeytingLean.HeytingVeil.Route

def routeClassIdFor (route : BackendRoute) : String :=
  match route with
  | .lambdaIRMiniCC => "lambdair_minic_c"
  | .lambdaIROnly => "lambdair_only"
  | .miniCOnly => "minic_only"

def stableRouteClassIds : List String :=
  [ "lambdair_minic_c"
  , "lambdair_only"
  , "minic_only"
  ]

def previewRouteClassIds : List String :=
  [ "lambdair_highir_c" ]

def plannedRouteClassIds : List String :=
  [ "lambdair_highir_cpp"
  , "lambdair_highir_rust"
  ]

def knownRouteClassIds : List String :=
  stableRouteClassIds ++ previewRouteClassIds ++ plannedRouteClassIds ++ ["unknown"]

def isStableRouteClass (classId : String) : Bool :=
  stableRouteClassIds.contains classId

def isKnownRouteClass (classId : String) : Bool :=
  knownRouteClassIds.contains classId

def isPlannedRouteClass (classId : String) : Bool :=
  plannedRouteClassIds.contains classId

def isPreviewRouteClass (classId : String) : Bool :=
  previewRouteClassIds.contains classId

def isImplementedRouteClass (classId : String) : Bool :=
  isStableRouteClass classId || isPreviewRouteClass classId

def isCertifyingRouteClass (classId : String) : Bool :=
  isStableRouteClass classId

def rolloutStageForRouteClass (classId : String) : String :=
  if isStableRouteClass classId then "implemented"
  else if isPreviewRouteClass classId then "preview"
  else if isPlannedRouteClass classId then "planned"
  else "unknown"

def derivationPlanForRouteClass (classId : String) : List String :=
  match classId with
  | "lambdair_minic_c" => ["LambdaIR", "MiniC", "C"]
  | "lambdair_only" => ["LambdaIR"]
  | "minic_only" => ["MiniC", "C"]
  | "lambdair_highir_c" => ["LambdaIR", "HighIR", "C"]
  | "lambdair_highir_cpp" => ["LambdaIR", "HighIR", "CPP"]
  | "lambdair_highir_rust" => ["LambdaIR", "HighIR", "Rust"]
  | _ => []

def derivationEndpointFamilyForRouteClass (classId : String) : String :=
  match classId with
  | "lambdair_minic_c" => "native_c_family"
  | "minic_only" => "native_c_family"
  | "lambdair_highir_c" => "native_c_family"
  | "lambdair_highir_cpp" => "native_cpp_family"
  | "lambdair_highir_rust" => "native_rust_family"
  | "lambdair_only" => "lambdair_ir_family"
  | _ => "unknown_endpoint_family"

def backendFamilyRolloutReadyForRouteClass (classId : String) : Bool :=
  if isPlannedRouteClass classId then
    false
  else if isImplementedRouteClass classId then
    true
  else
    false

def backendFamilyRolloutReasonForRouteClass (classId : String) : String :=
  if isPlannedRouteClass classId then
    if classId = "lambdair_highir_cpp" then
      "awaiting_cpp_backend_implementation"
    else if classId = "lambdair_highir_rust" then
      "awaiting_rust_backend_implementation"
    else
      "awaiting_planned_route_implementation"
  else if isImplementedRouteClass classId then
    "implemented_route_class"
  else if isKnownRouteClass classId then
    "known_nonimplemented_route_class"
  else
    "unknown_route_class"

def backendFamilyRolloutWitnessTheoremIdsForReason (reason : String) : List String :=
  if reason = "awaiting_cpp_backend_implementation" then
    [ "HeytingLean.HeytingVeil.Route.plannedRouteClassNotImplementedFromFlag"
    , "HeytingLean.HeytingVeil.Route.plannedRouteClassDerivationContainsHighIR"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationEndsInCPP"
    , "HeytingLean.HeytingVeil.Package.plannedRouteDowngradesUnverified"
    ]
  else if reason = "awaiting_rust_backend_implementation" then
    [ "HeytingLean.HeytingVeil.Route.plannedRouteClassNotImplementedFromFlag"
    , "HeytingLean.HeytingVeil.Route.plannedRouteClassDerivationContainsHighIR"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationEndsInRust"
    , "HeytingLean.HeytingVeil.Package.plannedRouteDowngradesUnverified"
    ]
  else
    []

def backendFamilyRolloutWitnessTheoremIdsForRouteClass (classId : String) : List String :=
  backendFamilyRolloutWitnessTheoremIdsForReason
    (backendFamilyRolloutReasonForRouteClass classId)

def plannedPolicyTheoremIdsForRouteClass (classId : String) : List String :=
  if classId = "lambdair_highir_cpp" then
    [ "HeytingLean.HeytingVeil.Route.plannedRouteClassNotImplementedFromFlag"
    , "HeytingLean.HeytingVeil.Route.plannedRouteClassDerivationContainsHighIR"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationEndsInCPP"
    , "HeytingLean.HeytingVeil.Package.plannedRouteDowngradesUnverified"
    ]
  else if classId = "lambdair_highir_rust" then
    [ "HeytingLean.HeytingVeil.Route.plannedRouteClassNotImplementedFromFlag"
    , "HeytingLean.HeytingVeil.Route.plannedRouteClassDerivationContainsHighIR"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationEndsInRust"
    , "HeytingLean.HeytingVeil.Package.plannedRouteDowngradesUnverified"
    ]
  else if isPreviewRouteClass classId then
    [ "HeytingLean.HeytingVeil.Route.previewRouteClassImplementedFromFlag"
    , "HeytingLean.HeytingVeil.Route.previewRouteClassDerivationContainsHighIR"
    , "HeytingLean.HeytingVeil.Package.previewRouteDowngradesUnverified"
    , "HeytingLean.HeytingVeil.Package.previewRouteReadyDowngradesPromotionReason"
    ]
  else
    []

def previewPromotionWitnessIdsForRouteClass (classId : String) : List String :=
  if isPreviewRouteClass classId then
    [ "HeytingLean.HeytingVeil.HighIR.ToC.highIRToCPreservationBridge"
    , "HeytingLean.HeytingVeil.HighIR.ToC.highIRToCFailureBridge"
    ]
  else
    []

def previewSemanticsWitnessIdsForRouteClass (classId : String) : List String :=
  if isPreviewRouteClass classId then
    [ "HeytingLean.HeytingVeil.HighIR.Semantics.execTransferPreservesConservation"
    , "HeytingLean.HeytingVeil.HighIR.Semantics.execTransferNonzeroCodeNegative"
    ]
  else
    []

def plannedBackendReadinessWitnessIdsForRouteClass (classId : String) : List String :=
  if classId = "lambdair_highir_cpp" then
    [ "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge"
    , "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge"
    ]
  else if classId = "lambdair_highir_rust" then
    [ "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustPreservationBridge"
    , "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustFailureBridge"
    ]
  else
    []

def plannedEndpointRealizationTheoremIdsForRouteClass (classId : String) : List String :=
  if classId = "lambdair_highir_cpp" then
    [ "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge"
    , "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationEndsInCPP"
    ]
  else if classId = "lambdair_highir_rust" then
    [ "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustPreservationBridge"
    , "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustFailureBridge"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationEndsInRust"
    ]
  else
    []

def plannedRolloutBridgeStrategyForRouteClass (classId : String) : String :=
  if classId = "lambdair_highir_cpp" then
    "preview_highir_c_bridge"
  else if classId = "lambdair_highir_rust" then
    "preview_highir_rust_bridge"
  else
    "none"

def plannedRolloutBridgeWitnessIdsForRouteClass (classId : String) : List String :=
  if classId = "lambdair_highir_cpp" then
    [ "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge"
    , "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationEndsInCPP"
    ]
  else if classId = "lambdair_highir_rust" then
    [ "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustPreservationBridge"
    , "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustFailureBridge"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationPlanExact"
    , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationEndsInRust"
    ]
  else
    []

def plannedRolloutBridgeReadyForRouteClass (classId : String) : Bool :=
  isPlannedRouteClass classId
    && plannedRolloutBridgeStrategyForRouteClass classId ≠ "none"
    && !(plannedRolloutBridgeWitnessIdsForRouteClass classId).isEmpty

def plannedRolloutBridgeActionHooksForRouteClass (classId : String) : List String :=
  if plannedRolloutBridgeReadyForRouteClass classId then
    [ s!"heytingveil promote --bridge-plan {classId}"
    , s!"heytingveil package --route {classId} --certificate cab_export_v2 --dry-run"
    ]
  else
    []

def previewPromotionTransitionIdsForRouteClass (classId : String) : List String :=
  if isPreviewRouteClass classId then
    [ "HeytingLean.HeytingVeil.Route.previewPromotionGateEligibleImpliesTransitionReady"
    , "HeytingLean.HeytingVeil.Package.previewRouteReadyDowngradesPromotionReason"
    ]
  else
    []

def targetClassForTarget (target : String) : String :=
  if target = "c" then "native_c"
  else if target = "cpp" then "native_cpp"
  else if target = "rust" then "native_rust"
  else if target = "lambdair" then "lambdair_ir"
  else if target = "minic" then "minic_ir"
  else "unknown_target"

def supportsTargetClass (classId : String) (targetClass : String) : Bool :=
  match classId, targetClass with
  | "lambdair_minic_c", "native_c" => true
  | "lambdair_only", "lambdair_ir" => true
  | "minic_only", "native_c" => true
  | "minic_only", "minic_ir" => true
  | "lambdair_highir_c", "native_c" => true
  | "lambdair_highir_cpp", "native_cpp" => true
  | "lambdair_highir_rust", "native_rust" => true
  | _, _ => false

def targetRealizationReasonForRouteClass (classId targetClass : String) : String :=
  if supportsTargetClass classId targetClass then
    "target_supported"
  else if targetClass = "unknown_target" then
    "unknown_target_requested"
  else if isKnownRouteClass classId then
    "route_target_mismatch"
  else
    "unknown_route_class"

def targetRealizationCaseForRouteClass (classId targetClass : String) : String :=
  if supportsTargetClass classId targetClass then
    "supported_case"
  else if targetClass = "unknown_target" then
    "unknown_target_case"
  else if isKnownRouteClass classId then
    "known_route_mismatch_case"
  else
    "unknown_route_case"

def targetRealizationReasonForCase (caseId : String) : String :=
  match caseId with
  | "supported_case" => "target_supported"
  | "unknown_target_case" => "unknown_target_requested"
  | "known_route_mismatch_case" => "route_target_mismatch"
  | "unknown_route_case" => "unknown_route_class"
  | _ => "unknown_route_class"

/-- Sprint obligation `HV.Route.TargetRealizationReasonForCaseSupported`. -/
theorem targetRealizationReasonForCaseSupported :
    targetRealizationReasonForCase "supported_case" = "target_supported" := by
  rfl

/-- Sprint obligation `HV.Route.TargetRealizationReasonForCaseUnknownTarget`. -/
theorem targetRealizationReasonForCaseUnknownTarget :
    targetRealizationReasonForCase "unknown_target_case" = "unknown_target_requested" := by
  rfl

/-- Sprint obligation `HV.Route.TargetRealizationReasonForCaseKnownRouteMismatch`. -/
theorem targetRealizationReasonForCaseKnownRouteMismatch :
    targetRealizationReasonForCase "known_route_mismatch_case" = "route_target_mismatch" := by
  rfl

/-- Sprint obligation `HV.Route.TargetRealizationReasonForCaseUnknownRoute`. -/
theorem targetRealizationReasonForCaseUnknownRoute :
    targetRealizationReasonForCase "unknown_route_case" = "unknown_route_class" := by
  rfl

/-- Sprint obligation `HV.Route.TargetRealizationReasonMatchesCase`. -/
theorem targetRealizationReasonMatchesCase (classId targetClass : String) :
    targetRealizationReasonForCase (targetRealizationCaseForRouteClass classId targetClass)
      = targetRealizationReasonForRouteClass classId targetClass := by
  by_cases hSupports : supportsTargetClass classId targetClass = true
  · simp [targetRealizationCaseForRouteClass, targetRealizationReasonForRouteClass,
      targetRealizationReasonForCase, hSupports]
  · by_cases hTarget : targetClass = "unknown_target"
    · subst targetClass
      have hSupportsUnknown : supportsTargetClass classId "unknown_target" = false := by
        simp [supportsTargetClass]
      simp [targetRealizationCaseForRouteClass, targetRealizationReasonForRouteClass,
        targetRealizationReasonForCase, hSupportsUnknown]
    · by_cases hKnown : isKnownRouteClass classId = true
      · simp [targetRealizationCaseForRouteClass, targetRealizationReasonForRouteClass,
          targetRealizationReasonForCase, hSupports, hTarget, hKnown]
      · simp [targetRealizationCaseForRouteClass, targetRealizationReasonForRouteClass,
          targetRealizationReasonForCase, hSupports, hTarget, hKnown]

/-- Sprint obligation `HV.Route.TargetRealizationReasonSupported`. -/
theorem targetRealizationReasonSupported (classId targetClass : String)
    (h : supportsTargetClass classId targetClass = true) :
    targetRealizationReasonForRouteClass classId targetClass = "target_supported" := by
  simp [targetRealizationReasonForRouteClass, h]

/-- Sprint obligation `HV.Route.TargetRealizationReasonUnknownTarget`. -/
theorem targetRealizationReasonUnknownTarget (classId : String) :
    targetRealizationReasonForRouteClass classId "unknown_target" = "unknown_target_requested" := by
  simp [targetRealizationReasonForRouteClass, supportsTargetClass]

/-- Sprint obligation `HV.Route.TargetRealizationReasonKnownMismatch`. -/
theorem targetRealizationReasonKnownMismatch (classId targetClass : String)
    (hKnown : isKnownRouteClass classId = true)
    (hSupports : supportsTargetClass classId targetClass = false)
    (hTarget : targetClass ≠ "unknown_target") :
    targetRealizationReasonForRouteClass classId targetClass = "route_target_mismatch" := by
  simp [targetRealizationReasonForRouteClass, hSupports, hTarget, hKnown]

/-- Sprint obligation `HV.Route.TargetRealizationReasonUnknownRouteClass`. -/
theorem targetRealizationReasonUnknownRouteClass (classId targetClass : String)
    (hKnown : isKnownRouteClass classId = false)
    (hSupports : supportsTargetClass classId targetClass = false)
    (hTarget : targetClass ≠ "unknown_target") :
    targetRealizationReasonForRouteClass classId targetClass = "unknown_route_class" := by
  simp [targetRealizationReasonForRouteClass, hSupports, hTarget, hKnown]

/-- Sprint obligation `HV.Route.StableRouteClassesSupportKnownTargetClasses`. -/
theorem stableRouteClassesSupportKnownTargetClasses (route : BackendRoute) :
    supportsTargetClass
      (routeClassIdFor route)
      (targetClassForTarget
        (match route with
        | .lambdaIRMiniCC => "c"
        | .lambdaIROnly => "lambdair"
        | .miniCOnly => "minic"))
      = true := by
  cases route <;> simp [routeClassIdFor, targetClassForTarget, supportsTargetClass]

/-- Sprint obligation `HV.Route.RouteClassIdForIsStable`. -/
theorem routeClassIdForIsStable (route : BackendRoute) :
    isStableRouteClass (routeClassIdFor route) = true := by
  cases route <;> simp [isStableRouteClass, routeClassIdFor, stableRouteClassIds]

/-- Sprint obligation `HV.Route.RouteClassIdForNotPlanned`. -/
theorem routeClassIdForNotPlanned (route : BackendRoute) :
    isPlannedRouteClass (routeClassIdFor route) = false := by
  cases route <;> simp [isPlannedRouteClass, routeClassIdFor, plannedRouteClassIds]

/-- Sprint obligation `HV.Route.RouteClassIdForNotPreview`. -/
theorem routeClassIdForNotPreview (route : BackendRoute) :
    isPreviewRouteClass (routeClassIdFor route) = false := by
  cases route <;> simp [isPreviewRouteClass, routeClassIdFor, previewRouteClassIds]

/-- Sprint obligation `HV.Route.RouteClassIdForImplemented`. -/
theorem routeClassIdForImplemented (route : BackendRoute) :
    isImplementedRouteClass (routeClassIdFor route) = true := by
  cases route <;> simp [isImplementedRouteClass, isStableRouteClass, isPreviewRouteClass,
    routeClassIdFor, stableRouteClassIds, previewRouteClassIds]

/-- Sprint obligation `HV.Route.PlannedRouteClassNotImplemented`. -/
theorem plannedRouteClassNotImplemented (classId : String)
    (h : classId ∈ plannedRouteClassIds) :
    isImplementedRouteClass classId = false := by
  have hCases :
      classId = "lambdair_highir_cpp"
      ∨ classId = "lambdair_highir_rust" := by
    simpa [plannedRouteClassIds] using h
  rcases hCases with h1 | h2
  · simp [isImplementedRouteClass, isStableRouteClass, isPreviewRouteClass,
      stableRouteClassIds, previewRouteClassIds, h1]
  · simp [isImplementedRouteClass, isStableRouteClass, isPreviewRouteClass,
      stableRouteClassIds, previewRouteClassIds, h2]

/-- Sprint obligation `HV.Route.PlannedRouteClassNotImplementedFromFlag`. -/
theorem plannedRouteClassNotImplementedFromFlag (classId : String)
    (h : isPlannedRouteClass classId = true) :
    isImplementedRouteClass classId = false := by
  have h' : classId ∈ plannedRouteClassIds := by
    simpa [isPlannedRouteClass] using h
  exact plannedRouteClassNotImplemented classId h'

/-- Sprint obligation `HV.Route.RolloutStageImplementedForStableRoutes`. -/
theorem rolloutStageImplementedForStableRoutes (route : BackendRoute) :
    rolloutStageForRouteClass (routeClassIdFor route) = "implemented" := by
  have hStable : isStableRouteClass (routeClassIdFor route) = true :=
    routeClassIdForIsStable route
  simp [rolloutStageForRouteClass, hStable]

/-- Sprint obligation `HV.Route.RouteClassIdForDerivationPlan`. -/
theorem routeClassIdForDerivationPlan (route : BackendRoute) :
    derivationPlanForRouteClass (routeClassIdFor route)
      =
        (match route with
        | .lambdaIRMiniCC => ["LambdaIR", "MiniC", "C"]
        | .lambdaIROnly => ["LambdaIR"]
        | .miniCOnly => ["MiniC", "C"]) := by
  cases route <;> rfl

/-- Sprint obligation `HV.Route.PlannedRouteClassDerivationContainsHighIR`. -/
theorem plannedRouteClassDerivationContainsHighIR (classId : String)
    (h : isPlannedRouteClass classId = true) :
    "HighIR" ∈ derivationPlanForRouteClass classId := by
  have h' : classId ∈ plannedRouteClassIds := by
    simpa [isPlannedRouteClass] using h
  have hCases :
      classId = "lambdair_highir_cpp"
      ∨ classId = "lambdair_highir_rust" := by
    simpa [plannedRouteClassIds] using h'
  rcases hCases with h1 | h2
  · simp [derivationPlanForRouteClass, h1]
  · simp [derivationPlanForRouteClass, h2]

/-- Sprint obligation `HV.Route.PlannedHighIRCppDerivationPlanExact`. -/
theorem plannedHighIRCppDerivationPlanExact :
    derivationPlanForRouteClass "lambdair_highir_cpp" = ["LambdaIR", "HighIR", "CPP"] := by
  rfl

/-- Sprint obligation `HV.Route.PlannedHighIRRustDerivationPlanExact`. -/
theorem plannedHighIRRustDerivationPlanExact :
    derivationPlanForRouteClass "lambdair_highir_rust" = ["LambdaIR", "HighIR", "Rust"] := by
  rfl

/-- Sprint obligation `HV.Route.PlannedHighIRCppEndpointFamily`. -/
theorem plannedHighIRCppEndpointFamily :
    derivationEndpointFamilyForRouteClass "lambdair_highir_cpp" = "native_cpp_family" := by
  rfl

/-- Sprint obligation `HV.Route.PlannedHighIRRustEndpointFamily`. -/
theorem plannedHighIRRustEndpointFamily :
    derivationEndpointFamilyForRouteClass "lambdair_highir_rust" = "native_rust_family" := by
  rfl

/-- Sprint obligation `HV.Route.PreviewHighIRCEndpointFamily`. -/
theorem previewHighIRCEndpointFamily :
    derivationEndpointFamilyForRouteClass "lambdair_highir_c" = "native_c_family" := by
  rfl

/-- Sprint obligation `HV.Route.RouteClassIdForEndpointFamily`. -/
theorem routeClassIdForEndpointFamily (route : BackendRoute) :
    derivationEndpointFamilyForRouteClass (routeClassIdFor route)
      =
        (match route with
        | .lambdaIRMiniCC => "native_c_family"
        | .lambdaIROnly => "lambdair_ir_family"
        | .miniCOnly => "native_c_family") := by
  cases route <;> rfl

/-- Sprint obligation `HV.Route.BackendFamilyRolloutReadyPlannedCpp`. -/
theorem backendFamilyRolloutReadyPlannedCpp :
    backendFamilyRolloutReadyForRouteClass "lambdair_highir_cpp" = false := by
  simp [backendFamilyRolloutReadyForRouteClass, isPlannedRouteClass, plannedRouteClassIds]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutReadyPlannedRust`. -/
theorem backendFamilyRolloutReadyPlannedRust :
    backendFamilyRolloutReadyForRouteClass "lambdair_highir_rust" = false := by
  simp [backendFamilyRolloutReadyForRouteClass, isPlannedRouteClass, plannedRouteClassIds]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutReasonPlannedCpp`. -/
theorem backendFamilyRolloutReasonPlannedCpp :
    backendFamilyRolloutReasonForRouteClass "lambdair_highir_cpp"
      = "awaiting_cpp_backend_implementation" := by
  simp [backendFamilyRolloutReasonForRouteClass, isPlannedRouteClass, plannedRouteClassIds]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutReasonPlannedRust`. -/
theorem backendFamilyRolloutReasonPlannedRust :
    backendFamilyRolloutReasonForRouteClass "lambdair_highir_rust"
      = "awaiting_rust_backend_implementation" := by
  simp [backendFamilyRolloutReasonForRouteClass, isPlannedRouteClass, plannedRouteClassIds]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutWitnessReasonPlannedCpp`. -/
theorem backendFamilyRolloutWitnessReasonPlannedCpp :
    backendFamilyRolloutWitnessTheoremIdsForReason "awaiting_cpp_backend_implementation"
      = plannedPolicyTheoremIdsForRouteClass "lambdair_highir_cpp" := by
  simp [backendFamilyRolloutWitnessTheoremIdsForReason, plannedPolicyTheoremIdsForRouteClass]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutWitnessReasonPlannedRust`. -/
theorem backendFamilyRolloutWitnessReasonPlannedRust :
    backendFamilyRolloutWitnessTheoremIdsForReason "awaiting_rust_backend_implementation"
      = plannedPolicyTheoremIdsForRouteClass "lambdair_highir_rust" := by
  simp [backendFamilyRolloutWitnessTheoremIdsForReason, plannedPolicyTheoremIdsForRouteClass]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutWitnessIdsForRouteClassPlannedCpp`. -/
theorem backendFamilyRolloutWitnessIdsForRouteClassPlannedCpp :
    backendFamilyRolloutWitnessTheoremIdsForRouteClass "lambdair_highir_cpp"
      = plannedPolicyTheoremIdsForRouteClass "lambdair_highir_cpp" := by
  simp [backendFamilyRolloutWitnessTheoremIdsForRouteClass, backendFamilyRolloutReasonPlannedCpp,
    backendFamilyRolloutWitnessReasonPlannedCpp]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutWitnessIdsForRouteClassPlannedRust`. -/
theorem backendFamilyRolloutWitnessIdsForRouteClassPlannedRust :
    backendFamilyRolloutWitnessTheoremIdsForRouteClass "lambdair_highir_rust"
      = plannedPolicyTheoremIdsForRouteClass "lambdair_highir_rust" := by
  simp [backendFamilyRolloutWitnessTheoremIdsForRouteClass, backendFamilyRolloutReasonPlannedRust,
    backendFamilyRolloutWitnessReasonPlannedRust]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutWitnessIdsForImplementedStableRoutes`. -/
theorem backendFamilyRolloutWitnessIdsForImplementedStableRoutes (route : BackendRoute) :
    backendFamilyRolloutWitnessTheoremIdsForRouteClass (routeClassIdFor route) = [] := by
  cases route <;>
    simp [backendFamilyRolloutWitnessTheoremIdsForRouteClass, backendFamilyRolloutReasonForRouteClass,
      backendFamilyRolloutWitnessTheoremIdsForReason, routeClassIdFor, isPlannedRouteClass,
      plannedRouteClassIds, isImplementedRouteClass, isStableRouteClass, isPreviewRouteClass,
      stableRouteClassIds, previewRouteClassIds]

/-- Sprint obligation `HV.Route.BackendFamilyRolloutReadyStableRoutes`. -/
theorem backendFamilyRolloutReadyStableRoutes (route : BackendRoute) :
    backendFamilyRolloutReadyForRouteClass (routeClassIdFor route) = true := by
  cases route <;>
    simp [backendFamilyRolloutReadyForRouteClass, isPlannedRouteClass, plannedRouteClassIds,
      isImplementedRouteClass, isStableRouteClass, isPreviewRouteClass, routeClassIdFor,
      stableRouteClassIds, previewRouteClassIds]

/-- Sprint obligation `HV.Route.PlannedHighIRCppDerivationEndsInCPP`. -/
theorem plannedHighIRCppDerivationEndsInCPP :
    List.getLast (derivationPlanForRouteClass "lambdair_highir_cpp")
      (by simp [derivationPlanForRouteClass]) = "CPP" := by
  simp [derivationPlanForRouteClass]

/-- Sprint obligation `HV.Route.PlannedHighIRRustDerivationEndsInRust`. -/
theorem plannedHighIRRustDerivationEndsInRust :
    List.getLast (derivationPlanForRouteClass "lambdair_highir_rust")
      (by simp [derivationPlanForRouteClass]) = "Rust" := by
  simp [derivationPlanForRouteClass]

/-- Sprint obligation `HV.Route.PreviewRouteClassImplemented`. -/
theorem previewRouteClassImplemented (classId : String)
    (h : classId ∈ previewRouteClassIds) :
    isImplementedRouteClass classId = true := by
  have hCase : classId = "lambdair_highir_c" := by
    simpa [previewRouteClassIds] using h
  simp [isImplementedRouteClass, isStableRouteClass, isPreviewRouteClass,
    previewRouteClassIds, stableRouteClassIds, hCase]

/-- Sprint obligation `HV.Route.PreviewRouteClassImplementedFromFlag`. -/
theorem previewRouteClassImplementedFromFlag (classId : String)
    (h : isPreviewRouteClass classId = true) :
    isImplementedRouteClass classId = true := by
  have h' : classId ∈ previewRouteClassIds := by
    simpa [isPreviewRouteClass] using h
  exact previewRouteClassImplemented classId h'

/-- Sprint obligation `HV.Route.PreviewRouteClassDerivationContainsHighIR`. -/
theorem previewRouteClassDerivationContainsHighIR (classId : String)
    (h : isPreviewRouteClass classId = true) :
    "HighIR" ∈ derivationPlanForRouteClass classId := by
  have hCase : classId = "lambdair_highir_c" := by
    simpa [isPreviewRouteClass, previewRouteClassIds] using h
  simp [derivationPlanForRouteClass, hCase]

/-- Sprint obligation `HV.Route.RolloutStagePreviewForPreviewRoute`. -/
theorem rolloutStagePreviewForPreviewRoute (classId : String)
    (h : isPreviewRouteClass classId = true) :
    rolloutStageForRouteClass classId = "preview" := by
  have hNotStable : isStableRouteClass classId = false := by
    have hCase : classId = "lambdair_highir_c" := by
      simpa [isPreviewRouteClass, previewRouteClassIds] using h
    simp [isStableRouteClass, stableRouteClassIds, hCase]
  simp [rolloutStageForRouteClass, h, hNotStable]

/-- Sprint obligation `HV.Route.PreviewRouteClassNotCertifying`. -/
theorem previewRouteClassNotCertifying (classId : String)
    (h : isPreviewRouteClass classId = true) :
    isCertifyingRouteClass classId = false := by
  have hNotStable : isStableRouteClass classId = false := by
    have hCase : classId = "lambdair_highir_c" := by
      simpa [isPreviewRouteClass, previewRouteClassIds] using h
    simp [isStableRouteClass, stableRouteClassIds, hCase]
  simp [isCertifyingRouteClass, hNotStable]

/-- Sprint obligation `HV.Route.PlannedPolicyTheoremIdsEmptyForStableRoute`. -/
theorem plannedPolicyTheoremIdsEmptyForStableRoute (route : BackendRoute) :
    plannedPolicyTheoremIdsForRouteClass (routeClassIdFor route) = [] := by
  cases route <;> simp [plannedPolicyTheoremIdsForRouteClass, routeClassIdFor,
    isPreviewRouteClass, previewRouteClassIds]

/-- Sprint obligation `HV.Route.PlannedPolicyTheoremIdsNonemptyForPlannedClass`. -/
theorem plannedPolicyTheoremIdsNonemptyForPlannedClass (classId : String)
    (hPlanned : isPlannedRouteClass classId = true) :
    (plannedPolicyTheoremIdsForRouteClass classId).isEmpty = false := by
  have hPlannedIn : classId ∈ plannedRouteClassIds := by
    simpa [isPlannedRouteClass] using hPlanned
  have hCases :
      classId = "lambdair_highir_cpp"
      ∨ classId = "lambdair_highir_rust" := by
    simpa [plannedRouteClassIds] using hPlannedIn
  rcases hCases with hCpp | hRust
  · simp [plannedPolicyTheoremIdsForRouteClass, hCpp]
  · simp [plannedPolicyTheoremIdsForRouteClass, hRust]

/-- Sprint obligation `HV.Route.PlannedPolicyTheoremIdsNonemptyForPreviewClass`. -/
theorem plannedPolicyTheoremIdsNonemptyForPreviewClass (classId : String)
    (hPreview : isPreviewRouteClass classId = true) :
    (plannedPolicyTheoremIdsForRouteClass classId).isEmpty = false := by
  have hCase : classId = "lambdair_highir_c" := by
    simpa [isPreviewRouteClass, previewRouteClassIds] using hPreview
  simp [plannedPolicyTheoremIdsForRouteClass, hCase, isPreviewRouteClass, previewRouteClassIds]

/-- Sprint obligation `HV.Route.PreviewPromotionWitnessIdsNonemptyForPreviewClass`. -/
theorem previewPromotionWitnessIdsNonemptyForPreviewClass (classId : String)
    (hPreview : isPreviewRouteClass classId = true) :
    (previewPromotionWitnessIdsForRouteClass classId).isEmpty = false := by
  simp [previewPromotionWitnessIdsForRouteClass, hPreview]

/-- Sprint obligation `HV.Route.PreviewPromotionWitnessIdsEmptyForNonPreviewClass`. -/
theorem previewPromotionWitnessIdsEmptyForNonPreviewClass (classId : String)
    (hPreview : isPreviewRouteClass classId = false) :
    previewPromotionWitnessIdsForRouteClass classId = [] := by
  simp [previewPromotionWitnessIdsForRouteClass, hPreview]

/-- Sprint obligation `HV.Route.PreviewSemanticsWitnessIdsNonemptyForPreviewClass`. -/
theorem previewSemanticsWitnessIdsNonemptyForPreviewClass (classId : String)
    (hPreview : isPreviewRouteClass classId = true) :
    (previewSemanticsWitnessIdsForRouteClass classId).isEmpty = false := by
  simp [previewSemanticsWitnessIdsForRouteClass, hPreview]

/-- Sprint obligation `HV.Route.PreviewSemanticsWitnessIdsEmptyForNonPreviewClass`. -/
theorem previewSemanticsWitnessIdsEmptyForNonPreviewClass (classId : String)
    (hPreview : isPreviewRouteClass classId = false) :
    previewSemanticsWitnessIdsForRouteClass classId = [] := by
  simp [previewSemanticsWitnessIdsForRouteClass, hPreview]

/-- Sprint obligation `HV.Route.PlannedBackendReadinessWitnessIdsExactPlannedCpp`. -/
theorem plannedBackendReadinessWitnessIdsExactPlannedCpp :
    plannedBackendReadinessWitnessIdsForRouteClass "lambdair_highir_cpp"
      =
        [ "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge"
        , "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge"
        ] := by
  simp [plannedBackendReadinessWitnessIdsForRouteClass]

/-- Sprint obligation `HV.Route.PlannedBackendReadinessWitnessIdsExactPlannedRust`. -/
theorem plannedBackendReadinessWitnessIdsExactPlannedRust :
    plannedBackendReadinessWitnessIdsForRouteClass "lambdair_highir_rust"
      =
        [ "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustPreservationBridge"
        , "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustFailureBridge"
        ] := by
  simp [plannedBackendReadinessWitnessIdsForRouteClass]

/-- Sprint obligation `HV.Route.PlannedBackendReadinessWitnessIdsEmptyForNonPlannedClass`. -/
theorem plannedBackendReadinessWitnessIdsEmptyForNonPlannedClass (classId : String)
    (hCpp : classId ≠ "lambdair_highir_cpp")
    (hRust : classId ≠ "lambdair_highir_rust") :
    plannedBackendReadinessWitnessIdsForRouteClass classId = [] := by
  simp [plannedBackendReadinessWitnessIdsForRouteClass, hCpp, hRust]

/-- Sprint obligation `HV.Route.PlannedBackendReadinessWitnessIdsNonemptyForPlannedClass`. -/
theorem plannedBackendReadinessWitnessIdsNonemptyForPlannedClass (classId : String)
    (hPlanned : isPlannedRouteClass classId = true) :
    (plannedBackendReadinessWitnessIdsForRouteClass classId).isEmpty = false := by
  have hPlannedIn : classId ∈ plannedRouteClassIds := by
    simpa [isPlannedRouteClass] using hPlanned
  have hCases :
      classId = "lambdair_highir_cpp"
      ∨ classId = "lambdair_highir_rust" := by
    simpa [plannedRouteClassIds] using hPlannedIn
  rcases hCases with hCpp | hRust
  · simp [plannedBackendReadinessWitnessIdsForRouteClass, hCpp]
  · simp [plannedBackendReadinessWitnessIdsForRouteClass, hRust]

/-- Sprint obligation `HV.Route.PlannedEndpointRealizationTheoremIdsExactPlannedCpp`. -/
theorem plannedEndpointRealizationTheoremIdsExactPlannedCpp :
    plannedEndpointRealizationTheoremIdsForRouteClass "lambdair_highir_cpp"
      =
        [ "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge"
        , "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge"
        , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationPlanExact"
        , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationEndsInCPP"
        ] := by
  simp [plannedEndpointRealizationTheoremIdsForRouteClass]

/-- Sprint obligation `HV.Route.PlannedEndpointRealizationTheoremIdsExactPlannedRust`. -/
theorem plannedEndpointRealizationTheoremIdsExactPlannedRust :
    plannedEndpointRealizationTheoremIdsForRouteClass "lambdair_highir_rust"
      =
        [ "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustPreservationBridge"
        , "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustFailureBridge"
        , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationPlanExact"
        , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationEndsInRust"
        ] := by
  simp [plannedEndpointRealizationTheoremIdsForRouteClass]

/-- Sprint obligation `HV.Route.PlannedEndpointRealizationTheoremIdsEmptyForNonPlannedClass`. -/
theorem plannedEndpointRealizationTheoremIdsEmptyForNonPlannedClass (classId : String)
    (hCpp : classId ≠ "lambdair_highir_cpp")
    (hRust : classId ≠ "lambdair_highir_rust") :
    plannedEndpointRealizationTheoremIdsForRouteClass classId = [] := by
  simp [plannedEndpointRealizationTheoremIdsForRouteClass, hCpp, hRust]

/-- Sprint obligation `HV.Route.PlannedEndpointRealizationTheoremIdsNonemptyForPlannedClass`. -/
theorem plannedEndpointRealizationTheoremIdsNonemptyForPlannedClass (classId : String)
    (hPlanned : isPlannedRouteClass classId = true) :
    (plannedEndpointRealizationTheoremIdsForRouteClass classId).isEmpty = false := by
  have hPlannedIn : classId ∈ plannedRouteClassIds := by
    simpa [isPlannedRouteClass] using hPlanned
  have hCases :
      classId = "lambdair_highir_cpp"
      ∨ classId = "lambdair_highir_rust" := by
    simpa [plannedRouteClassIds] using hPlannedIn
  rcases hCases with hCpp | hRust
  · simp [plannedEndpointRealizationTheoremIdsForRouteClass, hCpp]
  · simp [plannedEndpointRealizationTheoremIdsForRouteClass, hRust]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeStrategyPlannedCpp`. -/
theorem plannedRolloutBridgeStrategyPlannedCpp :
    plannedRolloutBridgeStrategyForRouteClass "lambdair_highir_cpp" = "preview_highir_c_bridge" := by
  simp [plannedRolloutBridgeStrategyForRouteClass]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeStrategyPlannedRust`. -/
theorem plannedRolloutBridgeStrategyPlannedRust :
    plannedRolloutBridgeStrategyForRouteClass "lambdair_highir_rust"
      = "preview_highir_rust_bridge" := by
  simp [plannedRolloutBridgeStrategyForRouteClass]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeStrategyNonPlannedNone`. -/
theorem plannedRolloutBridgeStrategyNonPlannedNone (classId : String)
    (hCpp : classId ≠ "lambdair_highir_cpp")
    (hRust : classId ≠ "lambdair_highir_rust") :
    plannedRolloutBridgeStrategyForRouteClass classId = "none" := by
  simp [plannedRolloutBridgeStrategyForRouteClass, hCpp, hRust]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeWitnessIdsExactPlannedCpp`. -/
theorem plannedRolloutBridgeWitnessIdsExactPlannedCpp :
    plannedRolloutBridgeWitnessIdsForRouteClass "lambdair_highir_cpp"
      =
        [ "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge"
        , "HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge"
        , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationPlanExact"
        , "HeytingLean.HeytingVeil.Route.plannedHighIRCppDerivationEndsInCPP"
        ] := by
  simp [plannedRolloutBridgeWitnessIdsForRouteClass]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeWitnessIdsExactPlannedRust`. -/
theorem plannedRolloutBridgeWitnessIdsExactPlannedRust :
    plannedRolloutBridgeWitnessIdsForRouteClass "lambdair_highir_rust"
      =
        [ "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustPreservationBridge"
        , "HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustFailureBridge"
        , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationPlanExact"
        , "HeytingLean.HeytingVeil.Route.plannedHighIRRustDerivationEndsInRust"
        ] := by
  simp [plannedRolloutBridgeWitnessIdsForRouteClass]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeWitnessIdsEmptyNonPlanned`. -/
theorem plannedRolloutBridgeWitnessIdsEmptyNonPlanned (classId : String)
    (hCpp : classId ≠ "lambdair_highir_cpp")
    (hRust : classId ≠ "lambdair_highir_rust") :
    plannedRolloutBridgeWitnessIdsForRouteClass classId = [] := by
  simp [plannedRolloutBridgeWitnessIdsForRouteClass, hCpp, hRust]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeReadyPlannedCpp`. -/
theorem plannedRolloutBridgeReadyPlannedCpp :
    plannedRolloutBridgeReadyForRouteClass "lambdair_highir_cpp" = true := by
  simp [plannedRolloutBridgeReadyForRouteClass, isPlannedRouteClass, plannedRouteClassIds,
    plannedRolloutBridgeStrategyForRouteClass, plannedRolloutBridgeWitnessIdsForRouteClass]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeReadyPlannedRust`. -/
theorem plannedRolloutBridgeReadyPlannedRust :
    plannedRolloutBridgeReadyForRouteClass "lambdair_highir_rust" = true := by
  simp [plannedRolloutBridgeReadyForRouteClass, isPlannedRouteClass, plannedRouteClassIds,
    plannedRolloutBridgeStrategyForRouteClass, plannedRolloutBridgeWitnessIdsForRouteClass]

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeActionHooksPlannedCpp`. -/
theorem plannedRolloutBridgeActionHooksPlannedCpp :
    plannedRolloutBridgeActionHooksForRouteClass "lambdair_highir_cpp"
      =
        [ "heytingveil promote --bridge-plan lambdair_highir_cpp"
        , "heytingveil package --route lambdair_highir_cpp --certificate cab_export_v2 --dry-run"
        ] := by
  native_decide

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeActionHooksPlannedRust`. -/
theorem plannedRolloutBridgeActionHooksPlannedRust :
    plannedRolloutBridgeActionHooksForRouteClass "lambdair_highir_rust"
      =
        [ "heytingveil promote --bridge-plan lambdair_highir_rust"
        , "heytingveil package --route lambdair_highir_rust --certificate cab_export_v2 --dry-run"
        ] := by
  native_decide

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeActionHooksNonReadyEmpty`. -/
theorem plannedRolloutBridgeActionHooksNonReadyEmpty (classId : String)
    (hReady : plannedRolloutBridgeReadyForRouteClass classId = false) :
    plannedRolloutBridgeActionHooksForRouteClass classId = [] := by
  simp [plannedRolloutBridgeActionHooksForRouteClass, hReady]

/-- Sprint obligation `HV.Route.PreviewPromotionTransitionIdsNonemptyForPreviewClass`. -/
theorem previewPromotionTransitionIdsNonemptyForPreviewClass (classId : String)
    (hPreview : isPreviewRouteClass classId = true) :
    (previewPromotionTransitionIdsForRouteClass classId).isEmpty = false := by
  simp [previewPromotionTransitionIdsForRouteClass, hPreview]

/-- Sprint obligation `HV.Route.PreviewPromotionTransitionIdsEmptyForNonPreviewClass`. -/
theorem previewPromotionTransitionIdsEmptyForNonPreviewClass (classId : String)
    (hPreview : isPreviewRouteClass classId = false) :
    previewPromotionTransitionIdsForRouteClass classId = [] := by
  simp [previewPromotionTransitionIdsForRouteClass, hPreview]

/-- Sprint obligation `HV.Route.PreviewPromotionWitnessDeclarationsExist`. -/
theorem previewPromotionWitnessDeclarationsExist : True := by
  let _h1 := HeytingLean.HeytingVeil.HighIR.ToC.highIRToCPreservationBridge
  let _h2 := HeytingLean.HeytingVeil.HighIR.ToC.highIRToCFailureBridge
  trivial

/-- Sprint obligation `HV.Route.PreviewSemanticsWitnessDeclarationsExist`. -/
theorem previewSemanticsWitnessDeclarationsExist : True := by
  let _h1 :
      ∀ {pre post : HeytingLean.HeytingVeil.HighIR.Semantics.HighIRState} {code : Int},
        HeytingLean.HeytingVeil.HighIR.Semantics.execInstr
            HeytingLean.HeytingVeil.HighIR.Semantics.transferInstr pre post code
          -> HeytingLean.HeytingVeil.HighIR.Semantics.preservesConservation pre post :=
    HeytingLean.HeytingVeil.HighIR.Semantics.execTransferPreservesConservation
  let _h2 :
      ∀ {pre post : HeytingLean.HeytingVeil.HighIR.Semantics.HighIRState} {code : Int},
        HeytingLean.HeytingVeil.HighIR.Semantics.execInstr
            HeytingLean.HeytingVeil.HighIR.Semantics.transferInstr pre post code
          -> code ≠ 0
          -> code < 0 :=
    HeytingLean.HeytingVeil.HighIR.Semantics.execTransferNonzeroCodeNegative
  trivial

/-- Sprint obligation `HV.Route.PlannedBackendReadinessWitnessDeclarationsExist`. -/
theorem plannedBackendReadinessWitnessDeclarationsExist : True := by
  let _cpp1 := HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge
  let _cpp2 := HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge
  let _rust1 := HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustPreservationBridge
  let _rust2 := HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustFailureBridge
  trivial

/-- Sprint obligation `HV.Route.PlannedRolloutBridgeWitnessDeclarationsExist`. -/
theorem plannedRolloutBridgeWitnessDeclarationsExist : True := by
  let _cpp1 := HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge
  let _cpp2 := HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge
  let _cpp3 := plannedHighIRCppDerivationPlanExact
  let _cpp4 := plannedHighIRCppDerivationEndsInCPP
  trivial

/-- Sprint obligation `HV.Route.PlannedEndpointRealizationTheoremDeclarationsExist`. -/
theorem plannedEndpointRealizationTheoremDeclarationsExist : True := by
  let _cpp1 := HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPPreservationBridge
  let _cpp2 := HeytingLean.HeytingVeil.HighIR.ToCPP.highIRToCPPFailureBridge
  let _cpp3 := plannedHighIRCppDerivationPlanExact
  let _cpp4 := plannedHighIRCppDerivationEndsInCPP
  let _rust1 := HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustPreservationBridge
  let _rust2 := HeytingLean.HeytingVeil.HighIR.ToRust.highIRToRustFailureBridge
  let _rust3 := plannedHighIRRustDerivationPlanExact
  let _rust4 := plannedHighIRRustDerivationEndsInRust
  trivial

/-- Sprint obligation `HV.Route.PlannedRouteClassesAreKnown`. -/
theorem plannedRouteClassesAreKnown (classId : String)
    (h : classId ∈ plannedRouteClassIds) :
    isKnownRouteClass classId = true := by
  simp [isKnownRouteClass, knownRouteClassIds, h]

end HeytingLean.HeytingVeil.Route
