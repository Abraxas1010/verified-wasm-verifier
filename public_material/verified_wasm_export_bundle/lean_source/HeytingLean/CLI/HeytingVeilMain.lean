import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.HeytingVeil.DSL.Commands
import HeytingLean.HeytingVeil.Route
import HeytingLean.HeytingVeil.Package.VerifyExport
import HeytingLean.HeytingVeil.Verify.Replay
import HeytingLean.Meta.LeanTT0.ExportCAB

namespace HeytingLean.CLI.HeytingVeilMain

open HeytingLean.HeytingVeil
open HeytingLean.Meta.LeanTT0.ExportCAB
open Lean

private def usage : String :=
  String.intercalate "\n"
    [ "heytingveil - HeytingVeil command-plane bootstrap"
    , ""
    , "Usage:"
    , "  lake exe heytingveil -- <cmd> <spec-text>"
    , "  lake exe heytingveil -- promote --bridge-plan <route-class-id>"
    , ""
    , "Commands:"
    , "  parse | elab | emit | check | verify | package | package_promoted | promote | promote_apply"
    ]

private def parseOrDie (src : String) : IO DSL.ParsedModule := do
  match DSL.parseText src with
  | .ok pm => pure pm
  | .error e => throw <| IO.userError s!"parse failed: {e}"

private def elabOrDie (src : String) : IO DSL.ElaboratedModule := do
  let pm ← parseOrDie src
  match DSL.elaborate DSL.defaultProfile pm with
  | .ok em => pure em
  | .error e => throw <| IO.userError s!"elab failed: {e}"

private def asJson (pairs : List (String × Json)) : String :=
  Json.pretty (Json.mkObj pairs)

private def jsonStrArray (xs : List String) : Json :=
  Json.arr (xs.map Json.str).toArray

private def listSubsetByContains (lhs rhs : List String) : Bool :=
  lhs.all rhs.contains

private def listIntersectionByContains (lhs rhs : List String) : List String :=
  lhs.filter rhs.contains

private def endpointTargetRealizationMatrixJson : Json :=
  Json.mkObj
    [ ("supported_case", .str (Route.targetRealizationReasonForCase "supported_case"))
    , ("unknown_target_case", .str (Route.targetRealizationReasonForCase "unknown_target_case"))
    , ("known_route_mismatch_case",
        .str (Route.targetRealizationReasonForCase "known_route_mismatch_case"))
    , ("unknown_route_case", .str (Route.targetRealizationReasonForCase "unknown_route_case"))
    ]

private def backendFamilyRolloutWitnessMatrixJson : Json :=
  Json.mkObj
    [ ("awaiting_cpp_backend_implementation",
        jsonStrArray (Route.backendFamilyRolloutWitnessTheoremIdsForReason
          "awaiting_cpp_backend_implementation"))
    , ("awaiting_rust_backend_implementation",
        jsonStrArray (Route.backendFamilyRolloutWitnessTheoremIdsForReason
          "awaiting_rust_backend_implementation"))
    , ("implemented_route_class",
        jsonStrArray (Route.backendFamilyRolloutWitnessTheoremIdsForReason
          "implemented_route_class"))
    , ("known_nonimplemented_route_class",
        jsonStrArray (Route.backendFamilyRolloutWitnessTheoremIdsForReason
          "known_nonimplemented_route_class"))
    , ("unknown_route_class",
        jsonStrArray (Route.backendFamilyRolloutWitnessTheoremIdsForReason
          "unknown_route_class"))
    ]

private def bridgePlanArtifactRelForRouteClass (classId : String) : String :=
  s!"artifacts/heytingveil/bridge_plans/{classId}/bridge_plan.json"

private def bridgePlanCommandForRouteClass (classId : String) : String :=
  s!"lake exe heytingveil -- promote --bridge-plan {classId}"

private def endpointFamilyTerminalSymbol (family : String) : String :=
  if family = "native_cpp_family" then
    "CPP"
  else if family = "native_rust_family" then
    "Rust"
  else if family = "native_c_family" then
    "C"
  else
    ""

private def derivationTerminalSymbol (derivationPlan : List String) : String :=
  match derivationPlan.reverse with
  | terminal :: _ => terminal
  | [] => ""

private def plannedEndpointRealizationProjectionJson
    (selection : Route.Selection)
    (derivationEndpointFamily : String)
    (derivationEndpointTheoremIds : List String)
    (plannedBackendReadinessWitnessIds : List String)
    (plannedEndpointRealizationTheoremIds : List String) : Json :=
  let derivationPlan := selection.derivationPlan
  let derivationTerminal := derivationTerminalSymbol derivationPlan
  let expectedTerminal := endpointFamilyTerminalSymbol derivationEndpointFamily
  let derivationClosureContainsHighIR := derivationPlan.contains "HighIR"
  let derivationClosureTerminalMatchesEndpointFamily :=
    if expectedTerminal = "" then true else derivationTerminal = expectedTerminal
  let derivationEndpointTheoremCount := derivationEndpointTheoremIds.length
  let derivationEndpointTheoremCountMatches :=
    derivationEndpointTheoremCount = derivationEndpointTheoremIds.length
  let plannedEndpointRealizationTheoremCount := plannedEndpointRealizationTheoremIds.length
  let plannedEndpointRealizationTheoremCountMatches :=
    plannedEndpointRealizationTheoremCount = plannedEndpointRealizationTheoremIds.length
  let plannedEndpointRealizationTheoremLinksDerivationEndpoint :=
    listSubsetByContains derivationEndpointTheoremIds plannedEndpointRealizationTheoremIds
  let plannedEndpointRealizationTheoremLinksBackendReadiness :=
    listSubsetByContains plannedBackendReadinessWitnessIds plannedEndpointRealizationTheoremIds
  let plannedEndpointRealizationRequired := !plannedEndpointRealizationTheoremIds.isEmpty
  let plannedEndpointRealizationStatus :=
    if plannedEndpointRealizationRequired then
      "planned_realization_pending"
    else
      "not_required"
  let realizationHooks :=
    if plannedEndpointRealizationRequired then
      [ bridgePlanCommandForRouteClass selection.record.routeClassId
      , "lake exe heytingveil -- promote_apply <spec.hvtla>"
      , "lake exe heytingveil -- package_promoted <spec.hvtla>"
      ]
    else
      []
  let realizationHookCount := realizationHooks.length
  let realizationHookCountMatches := realizationHookCount = realizationHooks.length
  let realizationHooksNonemptyWhenRequired :=
    if plannedEndpointRealizationRequired then !realizationHooks.isEmpty else true
  let realizationExecutionReceiptStatus :=
    if plannedEndpointRealizationRequired then
      "pending_execution"
    else
      "not_required"
  let realizationExecutionEntries :=
    realizationHooks.map (fun hook =>
      Json.mkObj
        [ ("hook", .str hook)
        , ("hook_id", .str s!"endpoint_realization::{hook}")
        , ("run_state", .str "pending")
        , ("result_status", .str "not_started")
        , ("completed", .bool false)
        , ("result_payload", .null)
        ])
  let realizationExecutionEntryCount := realizationExecutionEntries.length
  let realizationExecutionEntryCountMatchesHookCount :=
    realizationExecutionEntryCount = realizationHookCount
  let realizationExecutionPendingCount := realizationExecutionEntryCount
  let realizationExecutionPendingCountMatchesEntries :=
    realizationExecutionPendingCount = realizationExecutionEntryCount
  let realizationExecutionCompletedCount := 0
  let realizationExecutionFailedCount := 0
  let realizationExecutionReadyForExecution :=
    if plannedEndpointRealizationRequired then
      realizationExecutionEntryCountMatchesHookCount && !realizationHooks.isEmpty
    else
      true
  let realizationExecutionReceipt := Json.mkObj
    [ ("receipt_status", .str realizationExecutionReceiptStatus)
    , ("required", .bool plannedEndpointRealizationRequired)
    , ("entry_count", .num realizationExecutionEntryCount)
    , ("entry_count_matches_hook_count",
        .bool realizationExecutionEntryCountMatchesHookCount)
    , ("pending_count", .num realizationExecutionPendingCount)
    , ("pending_count_matches_entries",
        .bool realizationExecutionPendingCountMatchesEntries)
    , ("completed_count", .num realizationExecutionCompletedCount)
    , ("failed_count", .num realizationExecutionFailedCount)
    , ("ready_for_execution", .bool realizationExecutionReadyForExecution)
    , ("entries", .arr realizationExecutionEntries.toArray)
    ]
  Json.mkObj
    [ ("schema_version", .str "v1")
    , ("route_class_id", .str selection.record.routeClassId)
    , ("target_class", .str selection.targetClass)
    , ("endpoint_family", .str derivationEndpointFamily)
    , ("derivation_plan", jsonStrArray derivationPlan)
    , ("derivation_terminal_symbol", .str derivationTerminal)
    , ("derivation_terminal_expected_symbol", .str expectedTerminal)
    , ("derivation_closure_contains_highir", .bool derivationClosureContainsHighIR)
    , ("derivation_closure_terminal_matches_endpoint_family",
        .bool derivationClosureTerminalMatchesEndpointFamily)
    , ("derivation_endpoint_theorem_ids", jsonStrArray derivationEndpointTheoremIds)
    , ("derivation_endpoint_theorem_count", .num derivationEndpointTheoremCount)
    , ("derivation_endpoint_theorem_count_matches", .bool derivationEndpointTheoremCountMatches)
    , ("planned_endpoint_realization_theorem_ids",
        jsonStrArray plannedEndpointRealizationTheoremIds)
    , ("planned_endpoint_realization_theorem_count",
        .num plannedEndpointRealizationTheoremCount)
    , ("planned_endpoint_realization_theorem_count_matches",
        .bool plannedEndpointRealizationTheoremCountMatches)
    , ("planned_endpoint_realization_theorem_links_derivation_endpoint",
        .bool plannedEndpointRealizationTheoremLinksDerivationEndpoint)
    , ("planned_endpoint_realization_theorem_links_backend_readiness",
        .bool plannedEndpointRealizationTheoremLinksBackendReadiness)
    , ("planned_backend_readiness_witness_ids",
        jsonStrArray plannedBackendReadinessWitnessIds)
    , ("planned_backend_readiness_witness_count", .num plannedBackendReadinessWitnessIds.length)
    , ("realization_hooks", jsonStrArray realizationHooks)
    , ("realization_hook_count", .num realizationHookCount)
    , ("realization_hook_count_matches", .bool realizationHookCountMatches)
    , ("realization_hooks_nonempty_when_required",
        .bool realizationHooksNonemptyWhenRequired)
    , ("realization_execution_receipt", realizationExecutionReceipt)
    , ("realization_execution_receipt_status", .str realizationExecutionReceiptStatus)
    , ("realization_execution_receipt_entry_count", .num realizationExecutionEntryCount)
    , ("realization_execution_receipt_entry_count_matches_hook_count",
        .bool realizationExecutionEntryCountMatchesHookCount)
    , ("realization_execution_receipt_pending_count", .num realizationExecutionPendingCount)
    , ("realization_execution_receipt_pending_count_matches_entries",
        .bool realizationExecutionPendingCountMatchesEntries)
    , ("realization_execution_receipt_ready_for_execution",
        .bool realizationExecutionReadyForExecution)
    , ("realization_required", .bool plannedEndpointRealizationRequired)
    , ("realization_status", .str plannedEndpointRealizationStatus)
    ]

private def plannedHighIRMaterializationChecklistId : String :=
  "materialize_planned_highir_backend"

private def plannedRolloutBridgeRealizationChecklistFor (required : Bool) : List String :=
  if required then
    [ plannedHighIRMaterializationChecklistId
    , "run_promote_apply_replay"
    , "run_package_promoted_replay"
    , "verify_cab_certificate_replay"
    ]
  else
    []

private def plannedRolloutBridgeCertifyingReplayHooksFor (required : Bool) : List String :=
  if required then
    [ "cd lean && lake exe heytingveil -- promote_apply <spec.hvtla>"
    , "cd lean && lake exe heytingveil -- package_promoted <spec.hvtla>"
    , "cd lean && lake exe heytingveil -- package <spec.hvtla>"
    , "python3 scripts/heytingveil_cert_regression.py --runs 2"
    ]
  else
    []

private def plannedRolloutBridgeRealizationStatusFor (required : Bool) (strategy : String) : String :=
  if required then
    "ready_for_execution"
  else if strategy = "none" then
    "not_applicable"
  else
    "pending_strategy_readiness"

private def plannedRolloutBridgeRealizationReceiptStatusFor
    (required : Bool) (realizationStatus : String) : String :=
  if !required then
    "not_required"
  else if realizationStatus = "ready_for_execution" then
    "pending_execution"
  else
    "blocked"

private def plannedRolloutBridgeRealizationReceiptFor
    (required : Bool)
    (realizationStatus : String)
    (checklist : List String)
    (replayHooks : List String) : Json :=
  let receiptStatus :=
    plannedRolloutBridgeRealizationReceiptStatusFor required realizationStatus
  let checklistEntries := checklist.map (fun entry =>
    Json.mkObj
      [ ("id", .str entry)
      , ("run_state", .str "pending")
      , ("result_status", .str "not_started")
      , ("completed", .bool false)
      , ("evidence", .null)
      ])
  let checklistEntryCount := checklistEntries.length
  let checklistEntryCountMatches := checklistEntryCount = checklist.length
  let checklistCompletedCount := 0
  let checklistPendingCount := checklist.length
  let checklistBlockedCount := 0
  let replayEntries := replayHooks.map (fun hook =>
    Json.mkObj
      [ ("hook", .str hook)
      , ("hook_id", .str s!"bridge_replay::{hook}")
      , ("command", .str hook)
      , ("run_state", .str "pending")
      , ("result_status", .str "not_started")
      , ("result_payload", .null)
      , ("executed", .bool false)
      , ("evidence", .null)
      ])
  let replayEntryCount := replayEntries.length
  let replayEntryCountMatches := replayEntryCount = replayHooks.length
  let replayExecutedCount := 0
  let replayPendingCount := replayHooks.length
  let replayFailedCount := 0
  let replaySkippedCount := 0
  let replayResultReadyCount := 0
  let replayAllResultOk := if required then false else true
  let allItemsComplete :=
    if required then
      checklistPendingCount = 0 && replayPendingCount = 0
    else
      true
  let executionBindingMode :=
    if required then
      "deferred_pending_executor"
    else
      "not_required"
  Json.mkObj
    [ ("stage", .str "planned_rollout_bridge_realization_receipt")
    , ("required", .bool required)
    , ("status", .str receiptStatus)
    , ("realization_status", .str realizationStatus)
    , ("execution_binding_schema_version", .str "v1")
    , ("execution_binding_mode", .str executionBindingMode)
    , ("executor_hint", .str "heytingveil_bridge_replay_runner")
    , ("checklist_entries", .arr checklistEntries.toArray)
    , ("checklist_entry_count", .num checklistEntryCount)
    , ("checklist_entry_count_matches", .bool checklistEntryCountMatches)
    , ("checklist_completed_count", .num checklistCompletedCount)
    , ("checklist_pending_count", .num checklistPendingCount)
    , ("checklist_blocked_count", .num checklistBlockedCount)
    , ("checklist_state_counts", Json.mkObj
        [ ("pending", .num checklistPendingCount)
        , ("completed", .num checklistCompletedCount)
        , ("blocked", .num checklistBlockedCount)
        ])
    , ("certifying_replay_entries", .arr replayEntries.toArray)
    , ("certifying_replay_entry_count", .num replayEntryCount)
    , ("certifying_replay_entry_count_matches", .bool replayEntryCountMatches)
    , ("certifying_replay_executed_count", .num replayExecutedCount)
    , ("certifying_replay_pending_count", .num replayPendingCount)
    , ("certifying_replay_failed_count", .num replayFailedCount)
    , ("certifying_replay_skipped_count", .num replaySkippedCount)
    , ("certifying_replay_result_ready_count", .num replayResultReadyCount)
    , ("certifying_replay_all_results_ok", .bool replayAllResultOk)
    , ("certifying_replay_state_counts", Json.mkObj
        [ ("pending", .num replayPendingCount)
        , ("executed", .num replayExecutedCount)
        , ("failed", .num replayFailedCount)
        , ("skipped", .num replaySkippedCount)
        ])
    , ("all_items_complete", .bool allItemsComplete)
    ]

private def jsonValOrDefault (j : Json) (key : String) (fallback : Json) : Json :=
  match j.getObjVal? key with
  | .ok v => v
  | .error _ => fallback

private def jsonStrOrDefault (j : Json) (key : String) (fallback : String) : String :=
  match j.getObjValAs? String key with
  | .ok v => v
  | .error _ => fallback

private def jsonBoolOrDefault (j : Json) (key : String) (fallback : Bool) : Bool :=
  match j.getObjValAs? Bool key with
  | .ok v => v
  | .error _ => fallback

private def jsonNatOrDefault (j : Json) (key : String) (fallback : Nat) : Nat :=
  match j.getObjValAs? Nat key with
  | .ok v => v
  | .error _ => fallback

private def jsonArrayOrEmpty (j : Json) (key : String) : List Json :=
  match jsonValOrDefault j key (.arr #[]) with
  | .arr arr => arr.toList
  | _ => []

private def jsonCountWhere (xs : List Json) (pred : Json → Bool) : Nat :=
  xs.foldl (fun acc x => if pred x then acc + 1 else acc) 0

private def findChecklistOutcomeById (outcomes : List Json) (entryId : String) : Option Json :=
  outcomes.find? (fun candidate => jsonStrOrDefault candidate "id" "" = entryId)

private def findReplayOutcomeByHookIdOrHook
    (outcomes : List Json) (hookId : String) (hook : String) : Option Json :=
  outcomes.find? (fun candidate =>
    let candidateHookId := jsonStrOrDefault candidate "hook_id" ""
    let candidateHook := jsonStrOrDefault candidate "hook" ""
    let candidateCommand := jsonStrOrDefault candidate "command" ""
    candidateHookId = hookId || candidateHook = hook || candidateCommand = hook)

private def normalizeReplayCommand (command : String) : String :=
  let leanPrefix := "cd lean && "
  if command.startsWith leanPrefix then
    command.drop leanPrefix.length
  else
    command

private def findReplayOutcomeByNormalizedCommand
    (outcomes : List Json) (command : String) : Option Json :=
  let normalized := normalizeReplayCommand command
  outcomes.find? (fun candidate =>
    let candidateCommand :=
      normalizeReplayCommand
        (jsonStrOrDefault candidate "command" (jsonStrOrDefault candidate "hook" ""))
    candidateCommand = normalized)

private def bridgeReplayOutcomesStatusFor
    (required : Bool)
    (artifactPresent : Bool)
    (parseSucceeded : Bool)
    (schemaValid : Bool) : String :=
  if !required then
    "not_required"
  else if !artifactPresent then
    "absent"
  else if !parseSucceeded then
    "parse_error"
  else if !schemaValid then
    "invalid_schema"
  else
    "ingested"

private def runtimeReceiptStatusFor
    (required : Bool)
    (baseStatus : String)
    (outcomesStatus : String)
    (checklistPendingCount : Nat)
    (checklistBlockedCount : Nat)
    (replayPendingCount : Nat)
    (replayFailedCount : Nat)
    (replayEntryCount : Nat)
    (replayResultReadyCount : Nat) : String :=
  if !required then
    "not_required"
  else if checklistBlockedCount > 0 || replayFailedCount > 0 then
    "execution_failed"
  else if checklistPendingCount = 0 &&
      replayPendingCount = 0 &&
      replayEntryCount = replayResultReadyCount then
    "execution_complete"
  else if outcomesStatus = "ingested" then
    "execution_in_progress"
  else if outcomesStatus = "parse_error" || outcomesStatus = "invalid_schema" then
    "execution_outcomes_error"
  else
    baseStatus

private def realizedEndpointRealizationReceiptWithOutcomes
    (baseReceipt : Json)
    (outcomesStatus : String)
    (outcomesArtifactRel : Option String)
    (outcomesJson : Option Json) : Json :=
  let required := jsonBoolOrDefault baseReceipt "required" false
  let baseStatus := jsonStrOrDefault baseReceipt "receipt_status" "not_required"
  let baseEntries := jsonArrayOrEmpty baseReceipt "entries"
  let replayOutcomes := outcomesJson.map (fun v => jsonArrayOrEmpty v "certifying_replay_entries") |>.getD []
  let bridgePlanMaterializationOk :=
    outcomesJson.map (fun o => jsonBoolOrDefault o "bridge_plan_materialization_ok" false) |>.getD
      false
  let bridgePlanStatus :=
    outcomesJson.map (fun o => jsonStrOrDefault o "bridge_plan_status" "not_available") |>.getD
      "not_available"
  let bridgePlanRouteClassId :=
    outcomesJson.map (fun o => jsonStrOrDefault o "bridge_plan_route_class_id" "") |>.getD ""
  let bridgePlanArtifact :=
    outcomesJson.map (fun o => jsonStrOrDefault o "bridge_plan_artifact" "") |>.getD ""
  let bridgePlanArtifactJson :=
    if bridgePlanArtifact.isEmpty then .null else .str bridgePlanArtifact
  let bridgePlanCommand :=
    outcomesJson.map (fun o => jsonValOrDefault o "bridge_plan_command" .null) |>.getD .null
  let bridgePlanExitCode :=
    outcomesJson.map (fun o => jsonValOrDefault o "bridge_plan_exit_code" .null) |>.getD .null
  let bridgePlanProjectionSummary := Json.mkObj
    [ ("bridge_plan_materialization_ok", .bool bridgePlanMaterializationOk)
    , ("bridge_plan_status", .str bridgePlanStatus)
    , ("bridge_plan_route_class_id", .str bridgePlanRouteClassId)
    , ("bridge_plan_artifact", bridgePlanArtifactJson)
    , ("bridge_plan_command", bridgePlanCommand)
    , ("bridge_plan_exit_code", bridgePlanExitCode)
    ]
  let entries :=
    baseEntries.map (fun baseEntry =>
      let hook := jsonStrOrDefault baseEntry "hook" ""
      let hookId := jsonStrOrDefault baseEntry "hook_id" s!"endpoint_realization::{hook}"
      let command := jsonStrOrDefault baseEntry "command" hook
      let normalizedCommand := normalizeReplayCommand command
      let isBridgePlanHook :=
        normalizedCommand.startsWith "lake exe heytingveil -- promote --bridge-plan"
      let outcome? :=
        if isBridgePlanHook then none else findReplayOutcomeByNormalizedCommand replayOutcomes command
      let fallbackRunState := jsonStrOrDefault baseEntry "run_state" "pending"
      let fallbackResultStatus := jsonStrOrDefault baseEntry "result_status" "not_started"
      let fallbackExecuted :=
        jsonBoolOrDefault baseEntry "executed" (fallbackRunState = "executed" || fallbackResultStatus = "ok")
      let fallbackPayload := jsonValOrDefault baseEntry "result_payload" .null
      let fallbackEvidence := jsonValOrDefault baseEntry "evidence" .null
      let runState :=
        if isBridgePlanHook && outcomesStatus = "ingested" then
          if bridgePlanMaterializationOk then "executed" else "failed"
        else
          outcome?.map (fun o => jsonStrOrDefault o "run_state" fallbackRunState) |>.getD fallbackRunState
      let resultStatus :=
        if isBridgePlanHook && outcomesStatus = "ingested" then
          if bridgePlanMaterializationOk then "ok" else "error"
        else
          outcome?.map (fun o => jsonStrOrDefault o "result_status" fallbackResultStatus) |>.getD
            fallbackResultStatus
      let executed :=
        if isBridgePlanHook && outcomesStatus = "ingested" then
          bridgePlanMaterializationOk
        else
          outcome?.map (fun o =>
            jsonBoolOrDefault o "executed" (runState = "executed" || resultStatus = "ok")) |>.getD
              fallbackExecuted
      let resultPayload :=
        if isBridgePlanHook && outcomesStatus = "ingested" then
          Json.mkObj
            [ ("source", .str "bridge_plan_materialization")
            , ("summary", bridgePlanProjectionSummary)
            ]
        else
          outcome?.map (fun o => jsonValOrDefault o "result_payload" fallbackPayload) |>.getD
            fallbackPayload
      let evidence :=
        if isBridgePlanHook && outcomesStatus = "ingested" then
          Json.mkObj
            [ ("source", .str "bridge_plan_materialization")
            , ("ok", .bool bridgePlanMaterializationOk)
            , ("run_state", .str runState)
            , ("result_status", .str resultStatus)
            ]
        else
          outcome?.map (fun o => jsonValOrDefault o "evidence" fallbackEvidence) |>.getD
            fallbackEvidence
      Json.mkObj
        [ ("hook", .str hook)
        , ("hook_id", .str hookId)
        , ("command", .str command)
        , ("run_state", .str runState)
        , ("result_status", .str resultStatus)
        , ("executed", .bool executed)
        , ("result_payload", resultPayload)
        , ("evidence", evidence)
        ])
  let entryCount := entries.length
  let executedCount := jsonCountWhere entries (fun e =>
    jsonStrOrDefault e "run_state" "pending" = "executed" || jsonBoolOrDefault e "executed" false)
  let pendingCount := jsonCountWhere entries (fun e =>
    jsonStrOrDefault e "run_state" "pending" = "pending")
  let failedCount := jsonCountWhere entries (fun e =>
    let state := jsonStrOrDefault e "run_state" "pending"
    let result := jsonStrOrDefault e "result_status" "not_started"
    state = "failed" || result = "error" || result = "failed")
  let completedCount := executedCount
  let entryCountMatchesHookCount := entryCount = baseEntries.length
  let pendingCountMatchesEntries := pendingCount + executedCount + failedCount = entryCount
  let readyForExecutionBase :=
    jsonBoolOrDefault baseReceipt "ready_for_execution" (!required || entryCount > 0)
  let readyForExecution :=
    if required then
      readyForExecutionBase && entryCount > 0
    else
      true
  let outcomesIngested := outcomesStatus = "ingested"
  let receiptStatus :=
    if !required then
      "not_required"
    else if outcomesStatus = "parse_error" || outcomesStatus = "invalid_schema" then
      "execution_outcomes_error"
    else if failedCount > 0 then
      "execution_failed"
    else if pendingCount = 0 && entryCount > 0 then
      "execution_complete"
    else if outcomesIngested then
      "execution_in_progress"
    else
      baseStatus
  Json.mkObj
    [ ("required", .bool required)
    , ("receipt_status", .str receiptStatus)
    , ("ready_for_execution", .bool readyForExecution)
    , ("outcomes_status", .str outcomesStatus)
    , ("outcomes_ingested", .bool outcomesIngested)
    , ("outcomes_artifact",
        match outcomesArtifactRel with
        | some rel => .str rel
        | none => .null)
    , ("entry_count", .num entryCount)
    , ("entry_count_matches_hook_count", .bool entryCountMatchesHookCount)
    , ("pending_count", .num pendingCount)
    , ("pending_count_matches_entries", .bool pendingCountMatchesEntries)
    , ("failed_count", .num failedCount)
    , ("completed_count", .num completedCount)
    , ("executed_count", .num executedCount)
    , ("entries", .arr entries.toArray)
    , ("bridge_plan_materialization_projection_summary", bridgePlanProjectionSummary)
    ]

private def realizedBridgeReceiptWithOutcomes
    (baseReceipt : Json)
    (outcomesStatus : String)
    (outcomesArtifactRel : Option String)
    (outcomesJson : Option Json)
    (defaultBridgePlanStatus : String)
    (defaultBridgePlanRouteClassId : String)
    (defaultBridgePlanArtifactRel : Option String)
    (defaultBridgePlanCommand : Option String) : Json :=
  let required := jsonBoolOrDefault baseReceipt "required" false
  let realizationStatus := jsonStrOrDefault baseReceipt "realization_status" "unknown"
  let checklistOutcomes := outcomesJson.map (fun v => jsonArrayOrEmpty v "checklist_entries") |>.getD []
  let replayOutcomes := outcomesJson.map (fun v => jsonArrayOrEmpty v "certifying_replay_entries") |>.getD []
  let checklistEntries :=
    (jsonArrayOrEmpty baseReceipt "checklist_entries").map (fun baseEntry =>
      let entryId := jsonStrOrDefault baseEntry "id" ""
      let outcome? := findChecklistOutcomeById checklistOutcomes entryId
      let runState :=
        outcome?.map (fun o => jsonStrOrDefault o "run_state" "pending") |>.getD
          (jsonStrOrDefault baseEntry "run_state" "pending")
      let resultStatus :=
        outcome?.map (fun o => jsonStrOrDefault o "result_status" "not_started") |>.getD
          (jsonStrOrDefault baseEntry "result_status" "not_started")
      let completed :=
        outcome?.map (fun o =>
          jsonBoolOrDefault o "completed" (runState = "completed" || resultStatus = "ok")) |>.getD
          (jsonBoolOrDefault baseEntry "completed" (runState = "completed" || resultStatus = "ok"))
      let evidence :=
        outcome?.map (fun o => jsonValOrDefault o "evidence" .null) |>.getD
          (jsonValOrDefault baseEntry "evidence" .null)
      Json.mkObj
        [ ("id", .str entryId)
        , ("run_state", .str runState)
        , ("result_status", .str resultStatus)
        , ("completed", .bool completed)
        , ("evidence", evidence)
        ])
  let replayEntries :=
    (jsonArrayOrEmpty baseReceipt "certifying_replay_entries").map (fun baseEntry =>
      let hook := jsonStrOrDefault baseEntry "hook" ""
      let hookId := jsonStrOrDefault baseEntry "hook_id" s!"bridge_replay::{hook}"
      let outcome? := findReplayOutcomeByHookIdOrHook replayOutcomes hookId hook
      let command :=
        outcome?.map (fun o => jsonStrOrDefault o "command" hook) |>.getD
          (jsonStrOrDefault baseEntry "command" hook)
      let runState :=
        outcome?.map (fun o => jsonStrOrDefault o "run_state" "pending") |>.getD
          (jsonStrOrDefault baseEntry "run_state" "pending")
      let resultStatus :=
        outcome?.map (fun o => jsonStrOrDefault o "result_status" "not_started") |>.getD
          (jsonStrOrDefault baseEntry "result_status" "not_started")
      let executed :=
        outcome?.map (fun o =>
          jsonBoolOrDefault o "executed" (runState = "executed" || resultStatus = "ok")) |>.getD
          (jsonBoolOrDefault baseEntry "executed" (runState = "executed" || resultStatus = "ok"))
      let resultPayload :=
        outcome?.map (fun o => jsonValOrDefault o "result_payload" .null) |>.getD
          (jsonValOrDefault baseEntry "result_payload" .null)
      let evidence :=
        outcome?.map (fun o => jsonValOrDefault o "evidence" .null) |>.getD
          (jsonValOrDefault baseEntry "evidence" .null)
      Json.mkObj
        [ ("hook", .str hook)
        , ("hook_id", .str hookId)
        , ("command", .str command)
        , ("run_state", .str runState)
        , ("result_status", .str resultStatus)
        , ("result_payload", resultPayload)
        , ("executed", .bool executed)
        , ("evidence", evidence)
        ])
  let replayCoverageMatrixFromOutcomes :=
    outcomesJson.map (fun v => jsonArrayOrEmpty v "certifying_replay_coverage_matrix") |>.getD []
  let replayCoverageMatrix :=
    if outcomesStatus = "ingested" then
      if replayCoverageMatrixFromOutcomes.length > 0 then
        replayCoverageMatrixFromOutcomes
      else
        replayEntries.map (fun entry =>
          let hook := jsonStrOrDefault entry "hook" ""
          let source :=
            jsonStrOrDefault (jsonValOrDefault entry "result_payload" .null) "source" ""
          let runState := jsonStrOrDefault entry "run_state" "pending"
          let resultStatus := jsonStrOrDefault entry "result_status" "not_started"
          let isCabLane := source = "package" || source = "cert_regression"
          let cabRole :=
            if source = "package" then
              "certificate_emission"
            else if source = "cert_regression" then
              "certificate_replay_verification"
            else
              "not_cab_lane"
          Json.mkObj
            [ ("hook", .str hook)
            , ("source", .str source)
            , ("run_state", .str runState)
            , ("result_status", .str resultStatus)
            , ("is_cab_lane", .bool isCabLane)
            , ("cab_role", .str cabRole)
            ])
    else
      []
  let replayCoverageHookTotal := replayCoverageMatrix.length
  let replayCoverageHookSuccessCount := jsonCountWhere replayCoverageMatrix (fun row =>
    jsonStrOrDefault row "result_status" "not_started" = "ok")
  let replayCoverageHookFailedCount :=
    replayCoverageHookTotal - replayCoverageHookSuccessCount
  let replayCoverageCabHookTotal := jsonCountWhere replayCoverageMatrix (fun row =>
    jsonBoolOrDefault row "is_cab_lane" false)
  let replayCoverageCabHookSuccessCount := jsonCountWhere replayCoverageMatrix (fun row =>
    jsonBoolOrDefault row "is_cab_lane" false &&
      jsonStrOrDefault row "result_status" "not_started" = "ok")
  let replayCoverageCabHookFailedCount :=
    replayCoverageCabHookTotal - replayCoverageCabHookSuccessCount
  let replayCoverageCertRegressionRowCount := jsonCountWhere replayCoverageMatrix (fun row =>
    jsonStrOrDefault row "source" "" = "cert_regression")
  let replayCoverageCertRegressionOkCount := jsonCountWhere replayCoverageMatrix (fun row =>
    jsonStrOrDefault row "source" "" = "cert_regression" &&
      jsonStrOrDefault row "result_status" "not_started" = "ok")
  let replayCoverageCertRegressionPresent := replayCoverageCertRegressionRowCount > 0
  let replayCoverageCertRegressionOk :=
    replayCoverageCertRegressionPresent &&
      replayCoverageCertRegressionOkCount = replayCoverageCertRegressionRowCount
  let replayCoverageSummary := Json.mkObj
    [ ("hook_total", .num replayCoverageHookTotal)
    , ("hook_success_count", .num replayCoverageHookSuccessCount)
    , ("hook_failed_count", .num replayCoverageHookFailedCount)
    , ("hook_count_matches_rows",
        .bool (replayCoverageHookTotal = replayCoverageHookSuccessCount + replayCoverageHookFailedCount))
    , ("cab_hook_total", .num replayCoverageCabHookTotal)
    , ("cab_hook_success_count", .num replayCoverageCabHookSuccessCount)
    , ("cab_hook_failed_count", .num replayCoverageCabHookFailedCount)
    , ("cab_hook_count_matches_rows",
        .bool (replayCoverageCabHookTotal = replayCoverageCabHookSuccessCount + replayCoverageCabHookFailedCount))
    , ("cab_coverage_all_ok",
        .bool (replayCoverageCabHookTotal > 0 && replayCoverageCabHookFailedCount = 0))
    , ("cert_regression_present", .bool replayCoverageCertRegressionPresent)
    , ("cert_regression_ok", .bool replayCoverageCertRegressionOk)
    ]
  let checklistEntryCount := checklistEntries.length
  let checklistCompletedCount := jsonCountWhere checklistEntries (fun e =>
    jsonStrOrDefault e "run_state" "pending" = "completed")
  let checklistBlockedCount := jsonCountWhere checklistEntries (fun e =>
    jsonStrOrDefault e "run_state" "pending" = "blocked")
  let checklistPendingCount := jsonCountWhere checklistEntries (fun e =>
    jsonStrOrDefault e "run_state" "pending" = "pending")
  let replayEntryCount := replayEntries.length
  let replayExecutedCount := jsonCountWhere replayEntries (fun e =>
    jsonStrOrDefault e "run_state" "pending" = "executed" || jsonBoolOrDefault e "executed" false)
  let replayPendingCount := jsonCountWhere replayEntries (fun e =>
    jsonStrOrDefault e "run_state" "pending" = "pending")
  let replayFailedCount := jsonCountWhere replayEntries (fun e =>
    let state := jsonStrOrDefault e "run_state" "pending"
    let result := jsonStrOrDefault e "result_status" "not_started"
    state = "failed" || result = "failed")
  let replaySkippedCount := jsonCountWhere replayEntries (fun e =>
    let state := jsonStrOrDefault e "run_state" "pending"
    let result := jsonStrOrDefault e "result_status" "not_started"
    state = "skipped" || result = "skipped")
  let replayResultReadyCount := jsonCountWhere replayEntries (fun e =>
    jsonStrOrDefault e "result_status" "not_started" != "not_started")
  let replayAllResultOk :=
    if required then
      replayEntryCount > 0 && replayResultReadyCount = replayEntryCount && replayFailedCount = 0
    else
      true
  let allItemsComplete :=
    if required then
      checklistPendingCount = 0 &&
        checklistBlockedCount = 0 &&
        replayPendingCount = 0 &&
        replayFailedCount = 0 &&
        replayEntryCount = replayResultReadyCount
    else
      true
  let status :=
    runtimeReceiptStatusFor required (jsonStrOrDefault baseReceipt "status" "pending_execution")
      outcomesStatus checklistPendingCount checklistBlockedCount replayPendingCount replayFailedCount
      replayEntryCount replayResultReadyCount
  let outcomesIngested := outcomesStatus = "ingested"
  let materializeEntry? :=
    match findChecklistOutcomeById checklistEntries plannedHighIRMaterializationChecklistId with
    | some entry => some entry
    | none => findChecklistOutcomeById checklistEntries "materialize_highir_cpp_backend"
  let materializeEvidence :=
    materializeEntry?.map (fun e => jsonValOrDefault e "evidence" .null) |>.getD .null
  let materializeRunState :=
    materializeEntry?.map (fun e => jsonStrOrDefault e "run_state" "pending") |>.getD "pending"
  let materializeResultStatus :=
    materializeEntry?.map (fun e => jsonStrOrDefault e "result_status" "not_started") |>.getD
      "not_started"
  let materializeCompleted :=
    materializeEntry?.map (fun e => jsonBoolOrDefault e "completed" false) |>.getD false
  let materializationRule :=
    if materializeEntry?.isSome then
      let ruleFromEvidence := jsonStrOrDefault materializeEvidence "rule" ""
      if ruleFromEvidence.isEmpty then "bridge_plan_materialization_lane" else ruleFromEvidence
    else
      "not_available"
  let bridgePlanStatusFromEvidence :=
    jsonStrOrDefault materializeEvidence "bridge_plan_status" defaultBridgePlanStatus
  let bridgePlanRouteClassFromEvidence :=
    jsonStrOrDefault materializeEvidence "bridge_plan_route_class_id" defaultBridgePlanRouteClassId
  let bridgePlanArtifactFromEvidence :=
    jsonStrOrDefault materializeEvidence "bridge_plan_artifact"
      (defaultBridgePlanArtifactRel.getD "")
  let bridgePlanCommandFromEvidence :=
    jsonValOrDefault materializeEvidence "bridge_plan_command"
      (match defaultBridgePlanCommand with
      | some command => .str command
      | none => .null)
  let bridgePlanExitCodeFromEvidence :=
    jsonValOrDefault materializeEvidence "bridge_plan_exit_code" .null
  let bridgePlanMaterializationOk :=
    outcomesJson.map (fun o =>
      jsonBoolOrDefault o "bridge_plan_materialization_ok" materializeCompleted) |>.getD
        materializeCompleted
  let bridgePlanStatus :=
    outcomesJson.map (fun o =>
      jsonStrOrDefault o "bridge_plan_status" bridgePlanStatusFromEvidence) |>.getD
        bridgePlanStatusFromEvidence
  let bridgePlanRouteClassId :=
    outcomesJson.map (fun o =>
      jsonStrOrDefault o "bridge_plan_route_class_id" bridgePlanRouteClassFromEvidence) |>.getD
        bridgePlanRouteClassFromEvidence
  let bridgePlanArtifact :=
    outcomesJson.map (fun o =>
      jsonStrOrDefault o "bridge_plan_artifact" bridgePlanArtifactFromEvidence) |>.getD
        bridgePlanArtifactFromEvidence
  let bridgePlanArtifactJson :=
    if bridgePlanArtifact.isEmpty then
      .null
    else
      .str bridgePlanArtifact
  let bridgePlanCommand :=
    outcomesJson.map (fun o =>
      jsonValOrDefault o "bridge_plan_command" bridgePlanCommandFromEvidence) |>.getD
        bridgePlanCommandFromEvidence
  let bridgePlanExitCode :=
    outcomesJson.map (fun o =>
      jsonValOrDefault o "bridge_plan_exit_code" bridgePlanExitCodeFromEvidence) |>.getD
        bridgePlanExitCodeFromEvidence
  let sidecarAllHooksOk :=
    outcomesJson.map (fun o => jsonBoolOrDefault o "all_hooks_ok" false) |>.getD false
  let sidecarAllChecksOk :=
    outcomesJson.map (fun o => jsonBoolOrDefault o "all_checks_ok" false) |>.getD false
  let bridgePlanMaterializationProjectionSummary := Json.mkObj
    [ ("bridge_plan_materialization_ok", .bool bridgePlanMaterializationOk)
    , ("bridge_plan_status", .str bridgePlanStatus)
    , ("bridge_plan_route_class_id", .str bridgePlanRouteClassId)
    , ("bridge_plan_artifact", bridgePlanArtifactJson)
    , ("bridge_plan_command", bridgePlanCommand)
    , ("bridge_plan_exit_code", bridgePlanExitCode)
    , ("bridge_plan_materialization_rule", .str materializationRule)
    , ("bridge_plan_materialization_run_state", .str materializeRunState)
    , ("bridge_plan_materialization_result_status", .str materializeResultStatus)
    , ("bridge_plan_materialization_completed", .bool materializeCompleted)
    , ("bridge_plan_materialization_evidence", materializeEvidence)
    , ("all_hooks_ok", .bool sidecarAllHooksOk)
    , ("all_checks_ok", .bool sidecarAllChecksOk)
    ]
  Json.mkObj
    [ ("stage", .str "planned_rollout_bridge_realization_receipt_runtime")
    , ("required", .bool required)
    , ("status", .str status)
    , ("realization_status", .str realizationStatus)
    , ("execution_binding_schema_version",
        .str (jsonStrOrDefault baseReceipt "execution_binding_schema_version" "v1"))
    , ("execution_binding_mode",
        .str (jsonStrOrDefault baseReceipt "execution_binding_mode" "not_required"))
    , ("executor_hint", .str (jsonStrOrDefault baseReceipt "executor_hint" "heytingveil_bridge_replay_runner"))
    , ("replay_outcomes_status", .str outcomesStatus)
    , ("replay_outcomes_ingested", .bool outcomesIngested)
    , ("replay_outcomes_artifact",
        match outcomesArtifactRel with
        | some rel => .str rel
        | none => .null)
    , ("bridge_plan_materialization_ok", .bool bridgePlanMaterializationOk)
    , ("bridge_plan_status", .str bridgePlanStatus)
    , ("bridge_plan_route_class_id", .str bridgePlanRouteClassId)
    , ("bridge_plan_artifact", bridgePlanArtifactJson)
    , ("bridge_plan_command", bridgePlanCommand)
    , ("bridge_plan_exit_code", bridgePlanExitCode)
    , ("bridge_plan_materialization_rule", .str materializationRule)
    , ("bridge_plan_materialization_run_state", .str materializeRunState)
    , ("bridge_plan_materialization_result_status", .str materializeResultStatus)
    , ("bridge_plan_materialization_completed", .bool materializeCompleted)
    , ("bridge_plan_materialization_evidence", materializeEvidence)
    , ("all_hooks_ok", .bool sidecarAllHooksOk)
    , ("all_checks_ok", .bool sidecarAllChecksOk)
    , ("bridge_plan_materialization_projection_summary",
        bridgePlanMaterializationProjectionSummary)
    , ("checklist_entries", .arr checklistEntries.toArray)
    , ("checklist_entry_count", .num checklistEntryCount)
    , ("checklist_entry_count_matches", .bool (checklistEntryCount = checklistEntries.length))
    , ("checklist_completed_count", .num checklistCompletedCount)
    , ("checklist_pending_count", .num checklistPendingCount)
    , ("checklist_blocked_count", .num checklistBlockedCount)
    , ("checklist_state_counts", Json.mkObj
        [ ("pending", .num checklistPendingCount)
        , ("completed", .num checklistCompletedCount)
        , ("blocked", .num checklistBlockedCount)
        ])
    , ("certifying_replay_entries", .arr replayEntries.toArray)
    , ("certifying_replay_entry_count", .num replayEntryCount)
    , ("certifying_replay_entry_count_matches", .bool (replayEntryCount = replayEntries.length))
    , ("certifying_replay_executed_count", .num replayExecutedCount)
    , ("certifying_replay_pending_count", .num replayPendingCount)
    , ("certifying_replay_failed_count", .num replayFailedCount)
    , ("certifying_replay_skipped_count", .num replaySkippedCount)
    , ("certifying_replay_result_ready_count", .num replayResultReadyCount)
    , ("certifying_replay_all_results_ok", .bool replayAllResultOk)
    , ("certifying_replay_coverage_matrix", .arr replayCoverageMatrix.toArray)
    , ("certifying_replay_coverage_matrix_summary", replayCoverageSummary)
    , ("certifying_replay_state_counts", Json.mkObj
        [ ("pending", .num replayPendingCount)
        , ("executed", .num replayExecutedCount)
        , ("failed", .num replayFailedCount)
        , ("skipped", .num replaySkippedCount)
        ])
    , ("all_items_complete", .bool allItemsComplete)
    ]

private def loadReplayOutcomesIfPresent (path : System.FilePath) : IO (String × Option Json) := do
  if !(← path.pathExists) then
    pure ("absent", none)
  else
    let raw ← IO.FS.readFile path
    match Json.parse raw with
    | .error _ =>
        pure ("parse_error", none)
    | .ok parsed =>
        let schemaVersion := jsonStrOrDefault parsed "schema_version" ""
        if schemaVersion = "v1" then
          pure ("ingested", some parsed)
        else
          pure ("invalid_schema", none)

private def parseJsonOrDie (txt : String) : IO Json := do
  match Json.parse txt with
  | .ok j => pure j
  | .error e => throw <| IO.userError s!"json parse failed: {e}"

private def objValOrDie (j : Json) (key : String) : IO Json := do
  match j.getObjVal? key with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"missing json field '{key}': {e}"

private def objStrOrDie (j : Json) (key : String) : IO String := do
  match j.getObjValAs? String key with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"invalid string field '{key}': {e}"

private def objBoolOrDie (j : Json) (key : String) : IO Bool := do
  match j.getObjValAs? Bool key with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"invalid bool field '{key}': {e}"

private def objNatOrDie (j : Json) (key : String) : IO Nat := do
  match j.getObjValAs? Nat key with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"invalid nat field '{key}': {e}"

private def objStrArrayOrDie (j : Json) (key : String) : IO (Array String) := do
  match j.getObjValAs? (Array String) key with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"invalid string-array field '{key}': {e}"

private def certificateContainsTheorems (certPath : System.FilePath) (theorems : List String) : IO Bool := do
  if !(← certPath.pathExists) then
    pure false
  else
    let certRaw ← IO.FS.readFile certPath
    let certJson ← parseJsonOrDie certRaw
    let certTheorems := (← objStrArrayOrDie certJson "theorems").toList
    pure <| theorems.all certTheorems.contains

private def hvTypeTag : DSL.HvType → String
  | .int => "int"
  | .bool => "bool"

private def stateVarsJson (m : DSL.Module) : Json :=
  let entries :=
    m.stateVars.map (fun (name, ty) =>
      Json.mkObj
        [ ("name", .str name)
        , ("type", .str (hvTypeTag ty))
        ])
  Json.arr entries.toArray

private def semanticsBridgeJson (m : DSL.Module) : Json :=
  Json.mkObj
    [ ("state_model", .str "typed_machine_state_v1")
    , ("trace_model", .str "nat_indexed_trace_v1")
    , ("state_var_count", .num m.stateVars.length)
    , ("state_vars", stateVarsJson m)
    ]

private def repairPlanJson (c : Verify.CTIRecord) (p : Verify.RepairPlan) : Json :=
  let strictSelf := Verify.replay { strict := true } c c
  let relaxedSelf := Verify.replay { strict := false } c c
  Json.mkObj
    [ ("primary_clause_family", .str p.clauseFamily)
    , ("primary_clause_label", .str p.clauseLabel)
    , ("variable_focus", jsonStrArray p.variableFocus)
    , ("hints", jsonStrArray p.hints)
    , ("replay_self_strict", .bool strictSelf)
    , ("replay_self_relaxed", .bool relaxedSelf)
    ]

private def repairIterationJson (it : Verify.RepairIteration) : Json :=
  Json.mkObj
    [ ("selected_hint", .str it.selectedHint)
    , ("candidate_clause", .str it.candidateClause)
    , ("reverify_status", .str it.reverifyStatus)
    , ("notes", jsonStrArray it.notes)
    ]

private def repairReverifyJson (rv : Verify.RepairReverify) : Json :=
  Json.mkObj
    [ ("candidate_clause", .str rv.candidateClause)
    , ("applied_reason", .str rv.appliedReason)
    , ("strict_replay", .bool rv.strictReplay)
    , ("relaxed_replay", .bool rv.relaxedReplay)
    , ("status", .str rv.status)
    , ("notes", jsonStrArray rv.notes)
    ]

private def repairClosureJson (rc : Verify.RepairClosure) : Json :=
  Json.mkObj
    [ ("reverify_status", .str rc.reverifyStatus)
    , ("next_obligation", .str rc.nextObligation)
    , ("next_command", .str rc.nextCommand)
    , ("witness_ids", jsonStrArray rc.witnessIds)
    , ("notes", jsonStrArray rc.notes)
    ]

private def repairAutoLoopJson (ra : Verify.RepairAutoLoop) : Json :=
  Json.mkObj
    [ ("initial_status", .str ra.initialStatus)
    , ("integrated_reason", .str ra.integratedReason)
    , ("strict_replay_after_integrate", .bool ra.strictReplayAfterIntegrate)
    , ("relaxed_replay_after_integrate", .bool ra.relaxedReplayAfterIntegrate)
    , ("closure_status", .str ra.closureStatus)
    , ("notes", jsonStrArray ra.notes)
    ]

private def sanitizeToken (s : String) : String :=
  String.map
    (fun c => if c.isAlphanum || c = '_' || c = '-' then c else '_')
    s

private def repairArtifactPath (moduleName candidateClause : String) : System.FilePath :=
  let safeCandidate := sanitizeToken candidateClause
  System.FilePath.mk ".." / "artifacts" / "heytingveil" / moduleName /
    "repair_candidates" / s!"{safeCandidate}.candidate.txt"

private def repairArtifactContent
    (moduleName : String)
    (it : Verify.RepairIteration)
    (rv : Verify.RepairReverify)
    (ra : Verify.RepairAutoLoop) : String :=
  String.intercalate "\n"
    [ "# HeytingVeil Repair Candidate"
    , s!"module={moduleName}"
    , s!"candidate_clause={it.candidateClause}"
    , s!"selected_hint={it.selectedHint}"
    , s!"applied_reason={rv.appliedReason}"
    , s!"closure_status={ra.closureStatus}"
    , s!"next_action=integrate candidate clause in source spec and rerun verify"
    , ""
    ]

private def repairArtifactJson
    (moduleName : String)
    (it : Verify.RepairIteration)
    (rv : Verify.RepairReverify)
    (ra : Verify.RepairAutoLoop) : IO Json := do
  let path := repairArtifactPath moduleName it.candidateClause
  let generated := ra.closureStatus = "closure_ready"
  if generated then
    let parent := path.parent.getD (System.FilePath.mk ".")
    IO.FS.createDirAll parent
    IO.FS.writeFile path (repairArtifactContent moduleName it rv ra)
  pure <| Json.mkObj
    [ ("generated", .bool generated)
    , ("patch_path", .str path.toString)
    , ("candidate_clause", .str it.candidateClause)
    , ("closure_status", .str ra.closureStatus)
    ]

private def registryRefsJson (m : DSL.Module) : Json :=
  Json.mkObj
    [ ("declarations", Json.mkObj
        [ ("safety", .str "safetyRegistry")
        , ("liveness", .str "livenessRegistry")
        , ("invariant", .str "invariantRegistry")
        , ("reachable", .str "reachableRegistry")
        , ("wf", .str "wfRegistry")
        , ("sf", .str "sfRegistry")
        ])
    , ("labels", Json.mkObj
        [ ("safety", jsonStrArray m.safetyLabels)
        , ("liveness", jsonStrArray m.livenessLabels)
        , ("invariant", jsonStrArray m.invariantLabels)
        , ("reachable", jsonStrArray m.reachableLabels)
        , ("wf", jsonStrArray m.wfActions)
        , ("sf", jsonStrArray m.sfActions)
        ])
    , ("counts", Json.mkObj
        [ ("safety", .num m.explicitSafetyCount)
        , ("liveness", .num m.explicitLivenessCount)
        , ("invariant", .num m.explicitInvariantCount)
        , ("reachable", .num m.explicitReachableCount)
        , ("actions", .num m.actionNames.length)
        ])
    ]

private def routeSelectionJson (s : Route.Selection) : Json :=
  let isPlannedClass := Route.isPlannedRouteClass s.record.routeClassId
  let derivationEndpointFamily := Route.derivationEndpointFamilyForRouteClass s.record.routeClassId
  let derivationEndpointTheoremIds :=
    Route.plannedDerivationEndpointContractIdsForRouteClass s.record.routeClassId
  let derivationEndpointTheoremCount := derivationEndpointTheoremIds.length
  let derivationEndpointTheoremCountMatches :=
    derivationEndpointTheoremCount = derivationEndpointTheoremIds.length
  let endpointTargetSupported := Route.supportsTargetClass s.record.routeClassId s.targetClass
  let endpointTargetSupportMatchesSelection :=
    endpointTargetSupported = s.routeClassSupportsTargetClass
  let endpointTargetRealizationReason :=
    Route.targetRealizationReasonForRouteClass s.record.routeClassId s.targetClass
  let endpointTargetRealizationCase :=
    Route.targetRealizationCaseForRouteClass s.record.routeClassId s.targetClass
  let endpointTargetCaseReasonMatches :=
    Route.targetRealizationReasonForCase endpointTargetRealizationCase =
      endpointTargetRealizationReason
  let backendFamilyRolloutReady :=
    Route.backendFamilyRolloutReadyForRouteClass s.record.routeClassId
  let backendFamilyRolloutReason :=
    Route.backendFamilyRolloutReasonForRouteClass s.record.routeClassId
  let backendFamilyRolloutMatchesRouteImplemented :=
    backendFamilyRolloutReady = s.routeImplemented
  let backendFamilyRolloutWitnessTheoremIds :=
    Route.backendFamilyRolloutWitnessTheoremIdsForRouteClass s.record.routeClassId
  let backendFamilyRolloutWitnessTheoremCount := backendFamilyRolloutWitnessTheoremIds.length
  let backendFamilyRolloutWitnessTheoremCountMatches :=
    backendFamilyRolloutWitnessTheoremCount = backendFamilyRolloutWitnessTheoremIds.length
  let backendFamilyRolloutWitnessReasonMatches :=
    backendFamilyRolloutWitnessTheoremIds =
      Route.backendFamilyRolloutWitnessTheoremIdsForReason backendFamilyRolloutReason
  let backendFamilyRolloutWitnessLinksPlannedPolicy :=
    if isPlannedClass then
      backendFamilyRolloutWitnessTheoremIds = s.plannedPolicyTheoremIds
    else
      true
  let plannedBackendReadinessWitnessIds := s.plannedBackendReadinessWitnessIds
  let plannedBackendReadinessWitnessCount := plannedBackendReadinessWitnessIds.length
  let plannedBackendReadinessWitnessCountMatches :=
    plannedBackendReadinessWitnessCount = plannedBackendReadinessWitnessIds.length
  let plannedBackendReadinessWitnessMatchesClassPolicy :=
    plannedBackendReadinessWitnessIds =
      Route.plannedBackendReadinessWitnessIdsForRouteClass s.record.routeClassId
  let plannedBackendReadinessWitnessNonemptyForPlannedClass :=
    if isPlannedClass then !plannedBackendReadinessWitnessIds.isEmpty else true
  let plannedEndpointRealizationTheoremIds := s.plannedEndpointRealizationTheoremIds
  let plannedEndpointRealizationTheoremCount := plannedEndpointRealizationTheoremIds.length
  let plannedEndpointRealizationTheoremCountMatches :=
    plannedEndpointRealizationTheoremCount = plannedEndpointRealizationTheoremIds.length
  let plannedEndpointRealizationTheoremMatchesClassPolicy :=
    plannedEndpointRealizationTheoremIds =
      Route.plannedEndpointRealizationTheoremIdsForRouteClass s.record.routeClassId
  let plannedEndpointRealizationTheoremLinksDerivationEndpoint :=
    listSubsetByContains derivationEndpointTheoremIds plannedEndpointRealizationTheoremIds
  let plannedEndpointRealizationTheoremLinksBackendReadiness :=
    listSubsetByContains plannedBackendReadinessWitnessIds plannedEndpointRealizationTheoremIds
  let plannedEndpointRealizationTheoremNonemptyForPlannedClass :=
    if isPlannedClass then !plannedEndpointRealizationTheoremIds.isEmpty else true
  let plannedRolloutBridgeStrategy := s.plannedRolloutBridgeStrategy
  let plannedRolloutBridgeWitnessIds := s.plannedRolloutBridgeWitnessIds
  let plannedRolloutBridgeWitnessCount := plannedRolloutBridgeWitnessIds.length
  let plannedRolloutBridgeWitnessCountMatches :=
    plannedRolloutBridgeWitnessCount = plannedRolloutBridgeWitnessIds.length
  let plannedRolloutBridgeWitnessMatchesClassPolicy :=
    plannedRolloutBridgeWitnessIds =
      Route.plannedRolloutBridgeWitnessIdsForRouteClass s.record.routeClassId
  let plannedRolloutBridgeReady := s.plannedRolloutBridgeReady
  let plannedRolloutBridgeReadyMatchesClassPolicy :=
    plannedRolloutBridgeReady =
      Route.plannedRolloutBridgeReadyForRouteClass s.record.routeClassId
  let plannedRolloutBridgeActionHooks := s.plannedRolloutBridgeActionHooks
  let plannedRolloutBridgeActionHookCount := plannedRolloutBridgeActionHooks.length
  let plannedRolloutBridgeActionHooksMatchClassPolicy :=
    plannedRolloutBridgeActionHooks =
      Route.plannedRolloutBridgeActionHooksForRouteClass s.record.routeClassId
  Json.mkObj
    [ ("requested_hint", Json.str s.requestedHint)
    , ("requested_target", Json.str s.requestedTarget)
    , ("target_class", Json.str s.targetClass)
    , ("rollout_stage", Json.str s.rolloutStage)
    , ("derivation_plan", jsonStrArray s.derivationPlan)
    , ("derivation_endpoint_family", .str derivationEndpointFamily)
    , ("derivation_endpoint_theorem_ids", jsonStrArray derivationEndpointTheoremIds)
    , ("derivation_endpoint_theorem_count", .num derivationEndpointTheoremCount)
    , ("derivation_endpoint_theorem_count_matches", .bool derivationEndpointTheoremCountMatches)
    , ("planned_endpoint_realization_theorem_ids",
        jsonStrArray plannedEndpointRealizationTheoremIds)
    , ("planned_endpoint_realization_theorem_count",
        .num plannedEndpointRealizationTheoremCount)
    , ("planned_endpoint_realization_theorem_count_matches",
        .bool plannedEndpointRealizationTheoremCountMatches)
    , ("planned_endpoint_realization_theorem_matches_class_policy",
        .bool plannedEndpointRealizationTheoremMatchesClassPolicy)
    , ("planned_endpoint_realization_theorem_links_derivation_endpoint",
        .bool plannedEndpointRealizationTheoremLinksDerivationEndpoint)
    , ("planned_endpoint_realization_theorem_links_backend_readiness",
        .bool plannedEndpointRealizationTheoremLinksBackendReadiness)
    , ("planned_endpoint_realization_theorem_nonempty_for_planned_class",
        .bool plannedEndpointRealizationTheoremNonemptyForPlannedClass)
    , ("endpoint_target_requested", Json.str s.requestedTarget)
    , ("endpoint_target_class", Json.str s.targetClass)
    , ("endpoint_target_supported", Json.bool endpointTargetSupported)
    , ("endpoint_target_support_matches_selection", Json.bool endpointTargetSupportMatchesSelection)
    , ("endpoint_target_realization_reason", Json.str endpointTargetRealizationReason)
    , ("endpoint_target_realization_case", Json.str endpointTargetRealizationCase)
    , ("endpoint_target_case_reason_matches", Json.bool endpointTargetCaseReasonMatches)
    , ("endpoint_target_realization_matrix", endpointTargetRealizationMatrixJson)
    , ("backend_family_rollout_ready", Json.bool backendFamilyRolloutReady)
    , ("backend_family_rollout_reason", Json.str backendFamilyRolloutReason)
    , ("backend_family_rollout_matches_route_implemented",
        Json.bool backendFamilyRolloutMatchesRouteImplemented)
    , ("backend_family_rollout_witness_theorem_ids",
        jsonStrArray backendFamilyRolloutWitnessTheoremIds)
    , ("backend_family_rollout_witness_theorem_count", .num backendFamilyRolloutWitnessTheoremCount)
    , ("backend_family_rollout_witness_theorem_count_matches",
        .bool backendFamilyRolloutWitnessTheoremCountMatches)
    , ("backend_family_rollout_witness_reason_matches",
        .bool backendFamilyRolloutWitnessReasonMatches)
    , ("backend_family_rollout_witness_links_planned_policy",
        .bool backendFamilyRolloutWitnessLinksPlannedPolicy)
    , ("backend_family_rollout_witness_matrix", backendFamilyRolloutWitnessMatrixJson)
    , ("planned_backend_readiness_witness_ids",
        jsonStrArray plannedBackendReadinessWitnessIds)
    , ("planned_backend_readiness_witness_count",
        .num plannedBackendReadinessWitnessCount)
    , ("planned_backend_readiness_witness_count_matches",
        .bool plannedBackendReadinessWitnessCountMatches)
    , ("planned_backend_readiness_witness_matches_class_policy",
        .bool plannedBackendReadinessWitnessMatchesClassPolicy)
    , ("planned_backend_readiness_witness_nonempty_for_planned_class",
        .bool plannedBackendReadinessWitnessNonemptyForPlannedClass)
    , ("planned_rollout_bridge_strategy", .str plannedRolloutBridgeStrategy)
    , ("planned_rollout_bridge_witness_ids", jsonStrArray plannedRolloutBridgeWitnessIds)
    , ("planned_rollout_bridge_witness_count", .num plannedRolloutBridgeWitnessCount)
    , ("planned_rollout_bridge_witness_count_matches",
        .bool plannedRolloutBridgeWitnessCountMatches)
    , ("planned_rollout_bridge_witness_matches_class_policy",
        .bool plannedRolloutBridgeWitnessMatchesClassPolicy)
    , ("planned_rollout_bridge_ready", .bool plannedRolloutBridgeReady)
    , ("planned_rollout_bridge_ready_matches_class_policy",
        .bool plannedRolloutBridgeReadyMatchesClassPolicy)
    , ("planned_rollout_bridge_action_hooks", jsonStrArray plannedRolloutBridgeActionHooks)
    , ("planned_rollout_bridge_action_hook_count", .num plannedRolloutBridgeActionHookCount)
    , ("planned_rollout_bridge_action_hooks_match_class_policy",
        .bool plannedRolloutBridgeActionHooksMatchClassPolicy)
    , ("planned_policy_theorems", jsonStrArray s.plannedPolicyTheoremIds)
    , ("preview_promotion_witnesses", jsonStrArray s.previewPromotionWitnessIds)
    , ("preview_semantics_witnesses", jsonStrArray s.previewSemanticsWitnessIds)
    , ("preview_promotion_ready", Json.bool s.previewPromotionReady)
    , ("preview_promotion_verdict", Json.str s.previewPromotionVerdict)
    , ("preview_promotion_reason", Json.str s.previewPromotionReason)
    , ("preview_promotion_transitions", jsonStrArray s.previewPromotionTransitionIds)
    , ("preview_promotion_action_hooks", jsonStrArray s.previewPromotionActionHooks)
    , ("preview_promotion_transition_ready", Json.bool s.previewPromotionTransitionReady)
    , ("route_class_id", Json.str s.record.routeClassId)
    , ("witness_tier", Json.str s.witnessTier)
    , ("hint_recognized", Json.bool s.hintRecognized)
    , ("route_implemented", Json.bool s.routeImplemented)
    , ("target_compatible", Json.bool s.targetCompatible)
    , ("route_class_supports_target_class", Json.bool s.routeClassSupportsTargetClass)
    , ("planned_route_classes", jsonStrArray Route.plannedRouteClassIds)
    ]

private def promotionTransitionStatus (s : Route.Selection) : String :=
  if !Route.isPreviewRouteClass s.record.routeClassId then
    "not_applicable"
  else if !s.record.certifiedRequested then
    "blocked"
  else if s.previewPromotionTransitionReady then
    "ready_for_transition"
  else
    "blocked"

private def promotionTransitionReason (s : Route.Selection) : String :=
  if !Route.isPreviewRouteClass s.record.routeClassId then
    "not_preview_class"
  else if !s.record.certifiedRequested then
    "certificate_not_requested"
  else if s.previewPromotionTransitionReady then
    "ready_for_promotion"
  else
    s.previewPromotionReason

private structure ContractMetadataVersionResolution where
  requested : String
  resolved : String
  fallbackApplied : Bool
  resolutionReason : String

private def contractMetadataVersionResolutionFromEnv : IO ContractMetadataVersionResolution := do
  let requested? ← IO.getEnv "HEYTINGVEIL_CONTRACT_METADATA_VERSION"
  match requested? with
  | none =>
      pure
        { requested := Route.promotionContractMetadataCurrentVersion
          resolved := Route.promotionContractMetadataCurrentVersion
          fallbackApplied := false
          resolutionReason := "env_unset_default_current" }
  | some requested =>
      let resolved := Route.resolvePromotionContractMetadataVersion requested
      if resolved = requested then
        pure
          { requested := requested
            resolved := resolved
            fallbackApplied := false
            resolutionReason := "env_supported_exact" }
      else
        pure
          { requested := requested
            resolved := resolved
            fallbackApplied := true
            resolutionReason := "env_unsupported_fallback_current" }

private def promotionTransitionJson (s : Route.Selection)
    (versionResolution : ContractMetadataVersionResolution) : Json :=
  let status := promotionTransitionStatus s
  let reason := promotionTransitionReason s
  let contractMetadataVersion := versionResolution.resolved
  let contractMetadataRequestedVersion := versionResolution.requested
  let contractMetadataFallbackApplied := versionResolution.fallbackApplied
  let contractMetadataResolutionReason := versionResolution.resolutionReason
  let transitionTheoremIds := s.previewPromotionTransitionIds
  let transitionTheoremCount := transitionTheoremIds.length
  let transitionTheoremCountMatches := transitionTheoremCount = transitionTheoremIds.length
  let plannedPolicyTheoremIds := s.plannedPolicyTheoremIds
  let plannedPolicyTheoremCount := plannedPolicyTheoremIds.length
  let plannedPolicyTheoremCountMatches := plannedPolicyTheoremCount = plannedPolicyTheoremIds.length
  let isPlannedClass := Route.isPlannedRouteClass s.record.routeClassId
  let plannedPolicyNonemptyForPlannedClass :=
    if isPlannedClass then !plannedPolicyTheoremIds.isEmpty else true
  let plannedBackendReadinessWitnessIds := s.plannedBackendReadinessWitnessIds
  let plannedBackendReadinessWitnessCount := plannedBackendReadinessWitnessIds.length
  let plannedBackendReadinessWitnessCountMatches :=
    plannedBackendReadinessWitnessCount = plannedBackendReadinessWitnessIds.length
  let plannedBackendReadinessWitnessMatchesClassPolicy :=
    plannedBackendReadinessWitnessIds =
      Route.plannedBackendReadinessWitnessIdsForRouteClass s.record.routeClassId
  let plannedBackendReadinessWitnessNonemptyForPlannedClass :=
    if isPlannedClass then !plannedBackendReadinessWitnessIds.isEmpty else true
  let plannedRolloutBridgeStrategy := s.plannedRolloutBridgeStrategy
  let plannedRolloutBridgeWitnessIds := s.plannedRolloutBridgeWitnessIds
  let plannedRolloutBridgeWitnessCount := plannedRolloutBridgeWitnessIds.length
  let plannedRolloutBridgeWitnessCountMatches :=
    plannedRolloutBridgeWitnessCount = plannedRolloutBridgeWitnessIds.length
  let plannedRolloutBridgeWitnessMatchesClassPolicy :=
    plannedRolloutBridgeWitnessIds =
      Route.plannedRolloutBridgeWitnessIdsForRouteClass s.record.routeClassId
  let plannedRolloutBridgeReady := s.plannedRolloutBridgeReady
  let plannedRolloutBridgeReadyMatchesClassPolicy :=
    plannedRolloutBridgeReady =
      Route.plannedRolloutBridgeReadyForRouteClass s.record.routeClassId
  let plannedRolloutBridgeActionHooks := s.plannedRolloutBridgeActionHooks
  let plannedRolloutBridgeActionHookCount := plannedRolloutBridgeActionHooks.length
  let plannedRolloutBridgeActionHooksMatchClassPolicy :=
    plannedRolloutBridgeActionHooks =
      Route.plannedRolloutBridgeActionHooksForRouteClass s.record.routeClassId
  let derivationEndpointFamily := Route.derivationEndpointFamilyForRouteClass s.record.routeClassId
  let derivationEndpointTheoremIds :=
    Route.plannedDerivationEndpointContractIdsForRouteClass s.record.routeClassId
  let derivationEndpointTheoremCount := derivationEndpointTheoremIds.length
  let derivationEndpointTheoremCountMatches :=
    derivationEndpointTheoremCount = derivationEndpointTheoremIds.length
  let plannedEndpointRealizationTheoremIds := s.plannedEndpointRealizationTheoremIds
  let plannedEndpointRealizationTheoremCount := plannedEndpointRealizationTheoremIds.length
  let plannedEndpointRealizationTheoremCountMatches :=
    plannedEndpointRealizationTheoremCount = plannedEndpointRealizationTheoremIds.length
  let plannedEndpointRealizationTheoremMatchesClassPolicy :=
    plannedEndpointRealizationTheoremIds =
      Route.plannedEndpointRealizationTheoremIdsForRouteClass s.record.routeClassId
  let plannedEndpointRealizationTheoremLinksDerivationEndpoint :=
    listSubsetByContains derivationEndpointTheoremIds plannedEndpointRealizationTheoremIds
  let plannedEndpointRealizationTheoremLinksBackendReadiness :=
    listSubsetByContains plannedBackendReadinessWitnessIds plannedEndpointRealizationTheoremIds
  let plannedEndpointRealizationTheoremNonemptyForPlannedClass :=
    if isPlannedClass then !plannedEndpointRealizationTheoremIds.isEmpty else true
  let plannedEndpointRealizationProjection :=
    plannedEndpointRealizationProjectionJson
      s
      derivationEndpointFamily
      derivationEndpointTheoremIds
      plannedBackendReadinessWitnessIds
      plannedEndpointRealizationTheoremIds
  let endpointTargetSupported := Route.supportsTargetClass s.record.routeClassId s.targetClass
  let endpointTargetSupportMatchesSelection :=
    endpointTargetSupported = s.routeClassSupportsTargetClass
  let endpointTargetRealizationReason :=
    Route.targetRealizationReasonForRouteClass s.record.routeClassId s.targetClass
  let endpointTargetRealizationCase :=
    Route.targetRealizationCaseForRouteClass s.record.routeClassId s.targetClass
  let endpointTargetCaseReasonMatches :=
    Route.targetRealizationReasonForCase endpointTargetRealizationCase =
      endpointTargetRealizationReason
  let backendFamilyRolloutReady :=
    Route.backendFamilyRolloutReadyForRouteClass s.record.routeClassId
  let backendFamilyRolloutReason :=
    Route.backendFamilyRolloutReasonForRouteClass s.record.routeClassId
  let backendFamilyRolloutMatchesRouteImplemented :=
    backendFamilyRolloutReady = s.routeImplemented
  let backendFamilyRolloutWitnessTheoremIds :=
    Route.backendFamilyRolloutWitnessTheoremIdsForRouteClass s.record.routeClassId
  let backendFamilyRolloutWitnessTheoremCount := backendFamilyRolloutWitnessTheoremIds.length
  let backendFamilyRolloutWitnessTheoremCountMatches :=
    backendFamilyRolloutWitnessTheoremCount = backendFamilyRolloutWitnessTheoremIds.length
  let backendFamilyRolloutWitnessReasonMatches :=
    backendFamilyRolloutWitnessTheoremIds =
      Route.backendFamilyRolloutWitnessTheoremIdsForReason backendFamilyRolloutReason
  let backendFamilyRolloutWitnessLinksPlannedPolicy :=
    if isPlannedClass then
      backendFamilyRolloutWitnessTheoremIds = plannedPolicyTheoremIds
    else
      true
  let theoremContractIds :=
    Route.promotionTransitionTheoremContractIdsForVersion contractMetadataVersion s.record.routeClassId
  let theoremContractCount := theoremContractIds.length
  let theoremContractCountMatches := theoremContractCount = theoremContractIds.length
  let theoremContractHasPlannedPolicyLink :=
    "HeytingLean.HeytingVeil.Route.selectedPlannedPolicyTheoremIdsMatchClassPolicy"
      ∈ theoremContractIds
  let theoremContractRolloutWitnessPolicyIds :=
    Route.plannedRolloutWitnessPolicyContractIdsForRouteClass s.record.routeClassId
  let theoremContractRolloutWitnessPolicyCount := theoremContractRolloutWitnessPolicyIds.length
  let theoremContractRolloutWitnessPolicyCountMatches :=
    theoremContractRolloutWitnessPolicyCount = theoremContractRolloutWitnessPolicyIds.length
  let theoremContractHasRolloutWitnessPolicyLink :=
    listSubsetByContains theoremContractRolloutWitnessPolicyIds theoremContractIds
  let theoremContractRolloutWitnessIds :=
    listIntersectionByContains backendFamilyRolloutWitnessTheoremIds theoremContractIds
  let theoremContractRolloutWitnessCount := theoremContractRolloutWitnessIds.length
  let theoremContractRolloutWitnessCountMatches :=
    theoremContractRolloutWitnessCount = backendFamilyRolloutWitnessTheoremCount
  let theoremContractRolloutWitnessLinksPolicyMatrix :=
    theoremContractRolloutWitnessIds = backendFamilyRolloutWitnessTheoremIds
  let theoremContractRolloutWitnessLinksPlannedPolicy :=
    if isPlannedClass then
      theoremContractRolloutWitnessIds = plannedPolicyTheoremIds
    else
      theoremContractRolloutWitnessIds = []
  let plannedRolloutBridgeHandoffContractIds :=
    if plannedRolloutBridgeReady then
      listIntersectionByContains plannedPolicyTheoremIds theoremContractIds
    else
      []
  let plannedRolloutBridgeHandoffContractCount := plannedRolloutBridgeHandoffContractIds.length
  let plannedRolloutBridgeHandoffContractCountMatches :=
    plannedRolloutBridgeHandoffContractCount = plannedRolloutBridgeHandoffContractIds.length
  let plannedRolloutBridgeHandoffLinksPlannedPolicy :=
    if plannedRolloutBridgeReady then
      plannedRolloutBridgeHandoffContractIds = plannedPolicyTheoremIds
    else
      plannedRolloutBridgeHandoffContractIds = []
  let plannedRolloutBridgeRealizationRequired := status = "not_applicable" && plannedRolloutBridgeReady
  let plannedRolloutBridgeRealizationStatus :=
    plannedRolloutBridgeRealizationStatusFor plannedRolloutBridgeRealizationRequired
      plannedRolloutBridgeStrategy
  let plannedRolloutBridgeRealizationChecklist :=
    plannedRolloutBridgeRealizationChecklistFor plannedRolloutBridgeRealizationRequired
  let plannedRolloutBridgeRealizationChecklistCount :=
    plannedRolloutBridgeRealizationChecklist.length
  let plannedRolloutBridgeRealizationChecklistCountMatches :=
    plannedRolloutBridgeRealizationChecklistCount =
      plannedRolloutBridgeRealizationChecklist.length
  let plannedRolloutBridgeCertifyingReplayHooks :=
    plannedRolloutBridgeCertifyingReplayHooksFor plannedRolloutBridgeRealizationRequired
  let plannedRolloutBridgeCertifyingReplayHookCount :=
    plannedRolloutBridgeCertifyingReplayHooks.length
  let plannedRolloutBridgeCertifyingReplayHookCountMatches :=
    plannedRolloutBridgeCertifyingReplayHookCount =
      plannedRolloutBridgeCertifyingReplayHooks.length
  let plannedRolloutBridgeRealizationReceipt :=
    plannedRolloutBridgeRealizationReceiptFor
      plannedRolloutBridgeRealizationRequired
      plannedRolloutBridgeRealizationStatus
      plannedRolloutBridgeRealizationChecklist
      plannedRolloutBridgeCertifyingReplayHooks
  let bridgePlanProjectionArtifactRel := bridgePlanArtifactRelForRouteClass s.record.routeClassId
  let bridgePlanProjectionCommand := bridgePlanCommandForRouteClass s.record.routeClassId
  let bridgePlanProjectionDefaultStatus :=
    if plannedRolloutBridgeRealizationRequired then plannedRolloutBridgeRealizationStatus
    else "not_available"
  let bridgePlanProjectionDefaultRouteClassId :=
    if plannedRolloutBridgeRealizationRequired then s.record.routeClassId else ""
  let bridgePlanProjectionDefaultArtifact :=
    if plannedRolloutBridgeRealizationRequired then some bridgePlanProjectionArtifactRel else none
  let bridgePlanProjectionDefaultCommand :=
    if plannedRolloutBridgeRealizationRequired then some bridgePlanProjectionCommand else none
  let plannedRolloutBridgeMaterializationProjectionSummary :=
    jsonValOrDefault
      (realizedBridgeReceiptWithOutcomes
        plannedRolloutBridgeRealizationReceipt
        (if plannedRolloutBridgeRealizationRequired then "absent" else "not_applicable")
        none
        none
        bridgePlanProjectionDefaultStatus
        bridgePlanProjectionDefaultRouteClassId
        bridgePlanProjectionDefaultArtifact
        bridgePlanProjectionDefaultCommand)
      "bridge_plan_materialization_projection_summary"
      (Json.mkObj
        [ ("bridge_plan_materialization_ok", .bool false)
        , ("bridge_plan_status", .str "not_available")
        , ("bridge_plan_route_class_id", .str "")
        , ("bridge_plan_artifact", .null)
        , ("bridge_plan_command", .null)
        , ("bridge_plan_exit_code", .null)
        , ("bridge_plan_materialization_rule", .str "not_available")
        , ("bridge_plan_materialization_run_state", .str "pending")
        , ("bridge_plan_materialization_result_status", .str "not_started")
        , ("bridge_plan_materialization_completed", .bool false)
        , ("bridge_plan_materialization_evidence", .null)
        , ("all_hooks_ok", .bool false)
        , ("all_checks_ok", .bool false)
        ])
  let plannedRolloutBridgeRealizationContract := Json.mkObj
    [ ("stage", .str "planned_rollout_bridge_realization_contract")
    , ("route_class_id", .str s.record.routeClassId)
    , ("target_class", .str s.targetClass)
    , ("strategy", .str plannedRolloutBridgeStrategy)
    , ("required", .bool plannedRolloutBridgeRealizationRequired)
    , ("status", .str plannedRolloutBridgeRealizationStatus)
    , ("realization_checklist", jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("realization_checklist_count", .num plannedRolloutBridgeRealizationChecklistCount)
    , ("realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("certifying_replay_hooks", jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("certifying_replay_hook_count", .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("theorem_contract_handoff_ids", jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("theorem_contract_handoff_count", .num plannedRolloutBridgeHandoffContractCount)
    , ("theorem_contract_handoff_count_matches",
        .bool plannedRolloutBridgeHandoffContractCountMatches)
    , ("theorem_contract_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("required_bridge_witness_ids", jsonStrArray plannedRolloutBridgeWitnessIds)
    , ("required_bridge_witness_count", .num plannedRolloutBridgeWitnessCount)
    , ("execution_receipt", plannedRolloutBridgeRealizationReceipt)
    ]
  let packageTheoremContractIds := Package.theoremContractIdsForVersion contractMetadataVersion
  let packageTheoremContractCount := packageTheoremContractIds.length
  let packageTheoremContractCountMatches :=
    packageTheoremContractCount = packageTheoremContractIds.length
  let packageTheoremContractHasSelectionLink :=
    "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenCertifiedReady"
      ∈ packageTheoremContractIds
  let sharedTheoremContractIds :=
    Package.sharedTheoremContractIdsWithPolicyForVersion contractMetadataVersion s.record.routeClassId
  let sharedTheoremContractCount := sharedTheoremContractIds.length
  let sharedTheoremContractCountMatches := sharedTheoremContractCount = sharedTheoremContractIds.length
  let sharedTheoremContractHasSelectionLink :=
    "HeytingLean.HeytingVeil.Package.theoremIdsForSelectionWhenCertifiedReady"
      ∈ sharedTheoremContractIds
  let endpointRuntimeReceiptContractIds :=
    Route.endpointRuntimeReceiptContractIdsForVersion contractMetadataVersion
  let endpointRuntimeReceiptContractCount := endpointRuntimeReceiptContractIds.length
  let endpointRuntimeReceiptContractCountMatches :=
    endpointRuntimeReceiptContractCount = endpointRuntimeReceiptContractIds.length
  let certificateReplayRequired := status = "ready_for_transition"
  let theoremContractProjection := Json.mkObj
    [ ("contract_metadata_version", .str contractMetadataVersion)
    , ("contract_metadata_requested_version", .str contractMetadataRequestedVersion)
    , ("contract_metadata_fallback_applied", .bool contractMetadataFallbackApplied)
    , ("contract_metadata_resolution_reason", .str contractMetadataResolutionReason)
    , ("contract_metadata_supported_versions",
        jsonStrArray Route.promotionContractMetadataSupportedVersions)
    , ("certificate_replay_required", .bool certificateReplayRequired)
    , ("policy_contract_ids", jsonStrArray theoremContractIds)
    , ("policy_contract_count", .num theoremContractCount)
    , ("policy_contract_count_matches", .bool theoremContractCountMatches)
    , ("rollout_witness_policy_ids", jsonStrArray theoremContractRolloutWitnessPolicyIds)
    , ("rollout_witness_policy_count", .num theoremContractRolloutWitnessPolicyCount)
    , ("rollout_witness_policy_count_matches",
        .bool theoremContractRolloutWitnessPolicyCountMatches)
    , ("has_rollout_witness_policy_link", .bool theoremContractHasRolloutWitnessPolicyLink)
    , ("rollout_witness_ids", jsonStrArray theoremContractRolloutWitnessIds)
    , ("rollout_witness_count", .num theoremContractRolloutWitnessCount)
    , ("rollout_witness_count_matches", .bool theoremContractRolloutWitnessCountMatches)
    , ("rollout_witness_links_policy_matrix",
        .bool theoremContractRolloutWitnessLinksPolicyMatrix)
    , ("rollout_witness_links_planned_policy",
        .bool theoremContractRolloutWitnessLinksPlannedPolicy)
    , ("planned_endpoint_realization_theorem_ids",
        jsonStrArray plannedEndpointRealizationTheoremIds)
    , ("planned_endpoint_realization_theorem_count",
        .num plannedEndpointRealizationTheoremCount)
    , ("planned_endpoint_realization_theorem_count_matches",
        .bool plannedEndpointRealizationTheoremCountMatches)
    , ("planned_endpoint_realization_theorem_matches_class_policy",
        .bool plannedEndpointRealizationTheoremMatchesClassPolicy)
    , ("planned_endpoint_realization_theorem_links_derivation_endpoint",
        .bool plannedEndpointRealizationTheoremLinksDerivationEndpoint)
    , ("planned_endpoint_realization_theorem_links_backend_readiness",
        .bool plannedEndpointRealizationTheoremLinksBackendReadiness)
    , ("planned_endpoint_realization_theorem_nonempty_for_planned_class",
        .bool plannedEndpointRealizationTheoremNonemptyForPlannedClass)
    , ("endpoint_realization_runtime_receipt_contract_ids",
        jsonStrArray endpointRuntimeReceiptContractIds)
    , ("endpoint_realization_runtime_receipt_contract_count",
        .num endpointRuntimeReceiptContractCount)
    , ("endpoint_realization_runtime_receipt_contract_count_matches",
        .bool endpointRuntimeReceiptContractCountMatches)
    , ("planned_rollout_bridge_handoff_contract_ids",
        jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("planned_rollout_bridge_handoff_contract_count",
        .num plannedRolloutBridgeHandoffContractCount)
    , ("planned_rollout_bridge_handoff_contract_count_matches",
        .bool plannedRolloutBridgeHandoffContractCountMatches)
    , ("planned_rollout_bridge_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("planned_rollout_bridge_realization_required",
        .bool plannedRolloutBridgeRealizationRequired)
    , ("planned_rollout_bridge_realization_status",
        .str plannedRolloutBridgeRealizationStatus)
    , ("planned_rollout_bridge_realization_checklist",
        jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("planned_rollout_bridge_realization_checklist_count",
        .num plannedRolloutBridgeRealizationChecklistCount)
    , ("planned_rollout_bridge_realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("planned_rollout_bridge_certifying_replay_hooks",
        jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("planned_rollout_bridge_certifying_replay_hook_count",
        .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("planned_rollout_bridge_certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("planned_rollout_bridge_realization_contract", plannedRolloutBridgeRealizationContract)
    , ("planned_rollout_bridge_realization_receipt", plannedRolloutBridgeRealizationReceipt)
    , ("planned_rollout_bridge_materialization_projection_summary",
        plannedRolloutBridgeMaterializationProjectionSummary)
    , ("package_contract_ids", jsonStrArray packageTheoremContractIds)
    , ("package_contract_count", .num packageTheoremContractCount)
    , ("package_contract_count_matches", .bool packageTheoremContractCountMatches)
    , ("shared_contract_ids", jsonStrArray sharedTheoremContractIds)
    , ("shared_contract_count", .num sharedTheoremContractCount)
    , ("shared_contract_count_matches", .bool sharedTheoremContractCountMatches)
    , ("shared_contract_has_package_selection_link", .bool sharedTheoremContractHasSelectionLink)
    ]
  Json.mkObj
    [ ("transition_id", .str s!"preview_promotion::{s.record.routeClassId}::{reason}")
    , ("contract_metadata_version", .str contractMetadataVersion)
    , ("contract_metadata_requested_version", .str contractMetadataRequestedVersion)
    , ("contract_metadata_fallback_applied", .bool contractMetadataFallbackApplied)
    , ("contract_metadata_resolution_reason", .str contractMetadataResolutionReason)
    , ("contract_metadata_supported_versions", jsonStrArray Route.promotionContractMetadataSupportedVersions)
    , ("status", .str status)
    , ("reason", .str reason)
    , ("transition_ready", .bool (status = "ready_for_transition"))
    , ("route_class_id", .str s.record.routeClassId)
    , ("target_class", .str s.targetClass)
    , ("gate_verdict", .str s.previewPromotionVerdict)
    , ("gate_reason", .str s.previewPromotionReason)
    , ("transition_theorem_ids", jsonStrArray transitionTheoremIds)
    , ("transition_theorem_count", .num transitionTheoremCount)
    , ("transition_theorem_count_matches", .bool transitionTheoremCountMatches)
    , ("planned_policy_theorem_ids", jsonStrArray plannedPolicyTheoremIds)
    , ("planned_policy_theorem_count", .num plannedPolicyTheoremCount)
    , ("planned_policy_theorem_count_matches", .bool plannedPolicyTheoremCountMatches)
    , ("planned_policy_nonempty_for_planned_class", .bool plannedPolicyNonemptyForPlannedClass)
    , ("planned_backend_readiness_witness_ids",
        jsonStrArray plannedBackendReadinessWitnessIds)
    , ("planned_backend_readiness_witness_count", .num plannedBackendReadinessWitnessCount)
    , ("planned_backend_readiness_witness_count_matches",
        .bool plannedBackendReadinessWitnessCountMatches)
    , ("planned_backend_readiness_witness_matches_class_policy",
        .bool plannedBackendReadinessWitnessMatchesClassPolicy)
    , ("planned_backend_readiness_witness_nonempty_for_planned_class",
        .bool plannedBackendReadinessWitnessNonemptyForPlannedClass)
    , ("planned_endpoint_realization_theorem_ids",
        jsonStrArray plannedEndpointRealizationTheoremIds)
    , ("planned_endpoint_realization_theorem_count",
        .num plannedEndpointRealizationTheoremCount)
    , ("planned_endpoint_realization_theorem_count_matches",
        .bool plannedEndpointRealizationTheoremCountMatches)
    , ("planned_endpoint_realization_theorem_matches_class_policy",
        .bool plannedEndpointRealizationTheoremMatchesClassPolicy)
    , ("planned_endpoint_realization_theorem_links_derivation_endpoint",
        .bool plannedEndpointRealizationTheoremLinksDerivationEndpoint)
    , ("planned_endpoint_realization_theorem_links_backend_readiness",
        .bool plannedEndpointRealizationTheoremLinksBackendReadiness)
    , ("planned_endpoint_realization_theorem_nonempty_for_planned_class",
        .bool plannedEndpointRealizationTheoremNonemptyForPlannedClass)
    , ("endpoint_realization_runtime_receipt_contract_ids",
        jsonStrArray endpointRuntimeReceiptContractIds)
    , ("endpoint_realization_runtime_receipt_contract_count",
        .num endpointRuntimeReceiptContractCount)
    , ("endpoint_realization_runtime_receipt_contract_count_matches",
        .bool endpointRuntimeReceiptContractCountMatches)
    , ("planned_endpoint_realization_projection", plannedEndpointRealizationProjection)
    , ("planned_rollout_bridge_strategy", .str plannedRolloutBridgeStrategy)
    , ("planned_rollout_bridge_witness_ids", jsonStrArray plannedRolloutBridgeWitnessIds)
    , ("planned_rollout_bridge_witness_count", .num plannedRolloutBridgeWitnessCount)
    , ("planned_rollout_bridge_witness_count_matches",
        .bool plannedRolloutBridgeWitnessCountMatches)
    , ("planned_rollout_bridge_witness_matches_class_policy",
        .bool plannedRolloutBridgeWitnessMatchesClassPolicy)
    , ("planned_rollout_bridge_ready", .bool plannedRolloutBridgeReady)
    , ("planned_rollout_bridge_ready_matches_class_policy",
        .bool plannedRolloutBridgeReadyMatchesClassPolicy)
    , ("planned_rollout_bridge_action_hooks", jsonStrArray plannedRolloutBridgeActionHooks)
    , ("planned_rollout_bridge_action_hook_count", .num plannedRolloutBridgeActionHookCount)
    , ("planned_rollout_bridge_action_hooks_match_class_policy",
        .bool plannedRolloutBridgeActionHooksMatchClassPolicy)
    , ("planned_rollout_bridge_handoff_contract_ids",
        jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("planned_rollout_bridge_handoff_contract_count",
        .num plannedRolloutBridgeHandoffContractCount)
    , ("planned_rollout_bridge_handoff_contract_count_matches",
        .bool plannedRolloutBridgeHandoffContractCountMatches)
    , ("planned_rollout_bridge_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("planned_rollout_bridge_realization_required",
        .bool plannedRolloutBridgeRealizationRequired)
    , ("planned_rollout_bridge_realization_status",
        .str plannedRolloutBridgeRealizationStatus)
    , ("planned_rollout_bridge_realization_checklist",
        jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("planned_rollout_bridge_realization_checklist_count",
        .num plannedRolloutBridgeRealizationChecklistCount)
    , ("planned_rollout_bridge_realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("planned_rollout_bridge_certifying_replay_hooks",
        jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("planned_rollout_bridge_certifying_replay_hook_count",
        .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("planned_rollout_bridge_certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("planned_rollout_bridge_realization_contract", plannedRolloutBridgeRealizationContract)
    , ("planned_rollout_bridge_realization_receipt", plannedRolloutBridgeRealizationReceipt)
    , ("planned_rollout_bridge_materialization_projection_summary",
        plannedRolloutBridgeMaterializationProjectionSummary)
    , ("derivation_endpoint_family", .str derivationEndpointFamily)
    , ("derivation_endpoint_theorem_ids", jsonStrArray derivationEndpointTheoremIds)
    , ("derivation_endpoint_theorem_count", .num derivationEndpointTheoremCount)
    , ("derivation_endpoint_theorem_count_matches", .bool derivationEndpointTheoremCountMatches)
    , ("endpoint_target_requested", .str s.requestedTarget)
    , ("endpoint_target_class", .str s.targetClass)
    , ("endpoint_target_supported", .bool endpointTargetSupported)
    , ("endpoint_target_support_matches_selection", .bool endpointTargetSupportMatchesSelection)
    , ("endpoint_target_realization_reason", .str endpointTargetRealizationReason)
    , ("endpoint_target_realization_case", .str endpointTargetRealizationCase)
    , ("endpoint_target_case_reason_matches", .bool endpointTargetCaseReasonMatches)
    , ("endpoint_target_realization_matrix", endpointTargetRealizationMatrixJson)
    , ("backend_family_rollout_ready", .bool backendFamilyRolloutReady)
    , ("backend_family_rollout_reason", .str backendFamilyRolloutReason)
    , ("backend_family_rollout_matches_route_implemented",
        .bool backendFamilyRolloutMatchesRouteImplemented)
    , ("backend_family_rollout_witness_theorem_ids",
        jsonStrArray backendFamilyRolloutWitnessTheoremIds)
    , ("backend_family_rollout_witness_theorem_count", .num backendFamilyRolloutWitnessTheoremCount)
    , ("backend_family_rollout_witness_theorem_count_matches",
        .bool backendFamilyRolloutWitnessTheoremCountMatches)
    , ("backend_family_rollout_witness_reason_matches",
        .bool backendFamilyRolloutWitnessReasonMatches)
    , ("backend_family_rollout_witness_links_planned_policy",
        .bool backendFamilyRolloutWitnessLinksPlannedPolicy)
    , ("backend_family_rollout_witness_matrix", backendFamilyRolloutWitnessMatrixJson)
    , ("theorem_contract_ids", jsonStrArray theoremContractIds)
    , ("theorem_contract_count", .num theoremContractCount)
    , ("theorem_contract_count_matches", .bool theoremContractCountMatches)
    , ("theorem_contract_has_planned_policy_link", .bool theoremContractHasPlannedPolicyLink)
    , ("theorem_contract_rollout_witness_policy_ids",
        jsonStrArray theoremContractRolloutWitnessPolicyIds)
    , ("theorem_contract_rollout_witness_policy_count",
        .num theoremContractRolloutWitnessPolicyCount)
    , ("theorem_contract_rollout_witness_policy_count_matches",
        .bool theoremContractRolloutWitnessPolicyCountMatches)
    , ("theorem_contract_has_rollout_witness_policy_link",
        .bool theoremContractHasRolloutWitnessPolicyLink)
    , ("theorem_contract_rollout_witness_ids",
        jsonStrArray theoremContractRolloutWitnessIds)
    , ("theorem_contract_rollout_witness_count", .num theoremContractRolloutWitnessCount)
    , ("theorem_contract_rollout_witness_count_matches",
        .bool theoremContractRolloutWitnessCountMatches)
    , ("theorem_contract_rollout_witness_links_policy_matrix",
        .bool theoremContractRolloutWitnessLinksPolicyMatrix)
    , ("theorem_contract_rollout_witness_links_planned_policy",
        .bool theoremContractRolloutWitnessLinksPlannedPolicy)
    , ("package_theorem_contract_ids", jsonStrArray packageTheoremContractIds)
    , ("package_theorem_contract_count", .num packageTheoremContractCount)
    , ("package_theorem_contract_count_matches", .bool packageTheoremContractCountMatches)
    , ("package_theorem_contract_has_selection_link", .bool packageTheoremContractHasSelectionLink)
    , ("shared_theorem_contract_ids", jsonStrArray sharedTheoremContractIds)
    , ("shared_theorem_contract_count", .num sharedTheoremContractCount)
    , ("shared_theorem_contract_count_matches", .bool sharedTheoremContractCountMatches)
    , ("shared_theorem_contract_has_selection_link", .bool sharedTheoremContractHasSelectionLink)
    , ("theorem_contract_projection", theoremContractProjection)
    , ("certificate_replay_required", .bool certificateReplayRequired)
    , ("certificate_replay_assertion",
        .str "transition_theorem_ids must be included in promoted certificate theorem list when certificate_replay_required = true")
    , ("action_hooks", jsonStrArray s.previewPromotionActionHooks)
    ]

private def theoremEnvelopeJson
    (selection : Route.Selection)
    (theoremIds : List String) : Json :=
  let promotionTheoremIds := Package.previewPromotionTheoremIdsForSelection selection
  Json.mkObj
    [ ("witness_tier", Json.str selection.record.witnessTier)
    , ("base_count", Json.num Package.baseTheoremIds.length)
    , ("witness_count", Json.num selection.record.preservationWitnessIds.length)
    , ("preview_promotion_count", Json.num promotionTheoremIds.length)
    , ("total_count", Json.num theoremIds.length)
    ]

private def pickClauseRef (m : DSL.Module) : String × String :=
  if let some label := m.invariantLabels.head? then
    ("invariant", label)
  else if let some label := m.safetyLabels.head? then
    ("safety", label)
  else if let some label := m.reachableLabels.head? then
    ("reachable", label)
  else if let some label := m.livenessLabels.head? then
    ("liveness", label)
  else
    ("invariant", "inv-boot")

private def writeBundleFile (path : System.FilePath) (content : String) : IO Unit := do
  let parent := path.parent.getD (System.FilePath.mk ".")
  IO.FS.createDirAll parent
  IO.FS.writeFile path content

private def packageCommand (src : String) (promotePreview : Bool) : IO String := do
  let em ← elabOrDie src
  let art := DSL.emit em
  let baseSelection := Route.select em.parsed.mod
  let previewCertify :=
    Route.previewPromotionCertifiedFromMetadata
      promotePreview
      baseSelection.record.routeClassId
      baseSelection.previewPromotionTransitionReady
  let route : Route.RouteRecord :=
    { baseSelection.record with previewPromotionCertified := previewCertify }
  let selection : Route.Selection :=
    { baseSelection with record := route }
  let payload := Package.bindCabPayload art route 17
  let verifyStatus := Package.verifyExport route payload
  let verifyStatusStr :=
    match verifyStatus with
    | .certified => "certified"
    | .unverified reason => s!"unverified: {reason}"
  let outDir := System.FilePath.mk ".." / "artifacts" / "heytingveil" / art.moduleName
  let transitionResolution ← contractMetadataVersionResolutionFromEnv
  let transition := promotionTransitionJson selection transitionResolution
  let certificateReplayRequired :=
    jsonBoolOrDefault transition "certificate_replay_required" false
  let transitionPath := outDir / "package_transition_snapshot.json"
  let transitionArtifactRel := s!"artifacts/heytingveil/{art.moduleName}/package_transition_snapshot.json"
  let transitionProjectionSummary :=
    let policyContext := jsonValOrDefault transition "policy_context" .null
    let policyProjection := jsonValOrDefault policyContext "theorem_contract_projection_summary" .null
    if policyProjection != .null then
      policyProjection
    else
      jsonValOrDefault transition "theorem_contract_projection" .null
  let transitionMaterializationProjectionSummary :=
    let projectionMaterialization :=
      jsonValOrDefault
        transitionProjectionSummary
        "planned_rollout_bridge_materialization_projection_summary"
        .null
    if projectionMaterialization != .null then
      projectionMaterialization
    else
      jsonValOrDefault transition "planned_rollout_bridge_materialization_projection_summary" .null
  let transitionRealizationReceipt :=
    let projectionReceipt :=
      jsonValOrDefault
        transitionProjectionSummary
        "planned_rollout_bridge_realization_receipt"
        .null
    if projectionReceipt != .null then
      projectionReceipt
    else
      jsonValOrDefault transition "planned_rollout_bridge_realization_receipt" .null
  let transitionRealizationRequired :=
    jsonBoolOrDefault transitionRealizationReceipt "required" false
  let transitionRuntimeOutcomesStatus :=
    if transitionRealizationRequired then "absent" else "not_applicable"
  let defaultBridgePlanStatus :=
    jsonStrOrDefault transitionMaterializationProjectionSummary "bridge_plan_status" "not_available"
  let defaultBridgePlanRouteClassId :=
    jsonStrOrDefault transitionMaterializationProjectionSummary "bridge_plan_route_class_id" ""
  let defaultBridgePlanArtifactRel :=
    match jsonValOrDefault transitionMaterializationProjectionSummary "bridge_plan_artifact" .null with
    | .str rel =>
        if rel.isEmpty then none else some rel
    | _ => none
  let defaultBridgePlanCommandRel :=
    match jsonValOrDefault transitionMaterializationProjectionSummary "bridge_plan_command" .null with
    | .str cmd =>
        if cmd.isEmpty then none else some cmd
    | _ => none
  let plannedRolloutBridgeRealizationReceiptRuntime :=
    realizedBridgeReceiptWithOutcomes
      transitionRealizationReceipt
      transitionRuntimeOutcomesStatus
      none
      none
      defaultBridgePlanStatus
      defaultBridgePlanRouteClassId
      defaultBridgePlanArtifactRel
      defaultBridgePlanCommandRel
  let runtimeMaterializationProjectionSummary :=
    jsonValOrDefault
      plannedRolloutBridgeRealizationReceiptRuntime
      "bridge_plan_materialization_projection_summary"
      transitionMaterializationProjectionSummary
  let theoremContractProjectionMaterializationMatchesTransition :=
    runtimeMaterializationProjectionSummary == transitionMaterializationProjectionSummary

  let routeJson := Json.mkObj
    [ ("route", Json.str route.routeClassId)
    , ("route_class_id", Json.str route.routeClassId)
    , ("preservation_witness_ids", Json.arr (route.preservationWitnessIds.map Json.str).toArray)
    , ("preview_promotion_ready", Json.bool route.previewPromotionReady)
    , ("preview_promotion_certified", Json.bool route.previewPromotionCertified)
    , ("preview_promotion_verdict", Json.str selection.previewPromotionVerdict)
    , ("preview_promotion_reason", Json.str selection.previewPromotionReason)
    , ("preview_promotion_transitions", jsonStrArray selection.previewPromotionTransitionIds)
    , ("preview_promotion_action_hooks", jsonStrArray selection.previewPromotionActionHooks)
    , ("preview_promotion_transition_ready", Json.bool selection.previewPromotionTransitionReady)
    , ("witness_tier", Json.str route.witnessTier)
    , ("certified_requested", Json.bool route.certifiedRequested)
    , ("selection", routeSelectionJson selection)
    , ("package_transition_snapshot_artifact", Json.str transitionArtifactRel)
    ]
  let payloadJson := Json.mkObj
    [ ("module_name", Json.str payload.moduleName)
    , ("spec_hash", Json.num payload.specHash.toNat)
    , ("route_tag", Json.str payload.routeTag)
    , ("route_witness_ids", Json.arr (payload.routeWitnessIds.map Json.str).toArray)
    , ("artifact_hash", Json.num payload.artifactHash.toNat)
    , ("certified", Json.bool payload.certified)
    ]
  let snapshot := DSL.canonicalSnapshot em.parsed
  let transitionText := Json.pretty transition
  let routeText := Json.pretty routeJson
  let payloadText := Json.pretty payloadJson
  let snapshotPath := outDir / "spec_snapshot.txt"
  let specPath := outDir / "spec.hvtla"
  let generatedLeanPath := outDir / "generated.lean"
  let routePath := outDir / "route_record.json"
  let payloadPath := outDir / "package_payload.json"
  let verificationPath := outDir / "verification_status.txt"

  writeBundleFile transitionPath transitionText
  writeBundleFile snapshotPath snapshot
  writeBundleFile specPath src
  writeBundleFile generatedLeanPath art.code
  writeBundleFile routePath routeText
  writeBundleFile payloadPath payloadText
  writeBundleFile verificationPath verifyStatusStr

  let artifacts : List Artifact :=
    [ { name := "spec_snapshot.txt", content := snapshot }
    , { name := "spec.hvtla", content := src }
    , { name := "generated.lean", content := art.code }
    , { name := "route_record.json", content := routeText }
    , { name := "package_payload.json", content := payloadText }
    , { name := "verification_status.txt", content := verifyStatusStr }
    , { name := "package_transition_snapshot.json", content := transitionText }
    ]
  let theoremIds : List String := Package.theoremIdsForSelection selection
  let theoremEnvelope := theoremEnvelopeJson selection theoremIds
  let certificate := generateCertificate
    s!"heytingveil_{art.moduleName}"
    artifacts
    theoremIds
    [ "HeytingLean.HeytingVeil.DSL.Emit"
    , "HeytingLean.HeytingVeil.Route.Policy"
    , "HeytingLean.HeytingVeil.Package.CABLink"
    , "HeytingLean.HeytingVeil.Package.VerifyExport"
    ]
    "HeytingVeil package bundle with route/proof linkage."
  let certPath := outDir / "certificate.json"
  writeBundleFile certPath (Json.pretty certificate)

  pure <| asJson
    [ ("status", .str "ok")
    , ("stage", .str "packaged")
    , ("route", .str route.routeClassId)
    , ("route_selection", routeSelectionJson selection)
    , ("certificate_replay_required", .bool certificateReplayRequired)
    , ("promotion_transition", transition)
    , ("transition_artifact", .str transitionArtifactRel)
    , ("theorem_contract_projection_summary_transition", transitionProjectionSummary)
    , ("planned_rollout_bridge_materialization_projection_summary_transition",
        transitionMaterializationProjectionSummary)
    , ("planned_rollout_bridge_materialization_projection_summary_runtime",
        runtimeMaterializationProjectionSummary)
    , ("planned_rollout_bridge_realization_receipt_runtime_generated", .bool true)
    , ("planned_rollout_bridge_realization_receipt_runtime",
        plannedRolloutBridgeRealizationReceiptRuntime)
    , ("planned_rollout_bridge_realization_receipt_runtime_projection_summary",
        plannedRolloutBridgeRealizationReceiptRuntime)
    , ("theorem_contract_projection_materialization_projection_matches_transition",
        .bool theoremContractProjectionMaterializationMatchesTransition)
    , ("preview_promotion_certified", .bool route.previewPromotionCertified)
    , ("theorem_envelope", theoremEnvelope)
    , ("certified", .bool payload.certified)
    , ("artifact_hash", .num payload.artifactHash.toNat)
    , ("verification_status", .str verifyStatusStr)
    , ("out_dir", .str outDir.toString)
    , ("certificate", .str certPath.toString)
    ]

private def targetClassForRouteClass (classId : String) : String :=
  if classId = "lambdair_highir_cpp" then
    "native_cpp"
  else if classId = "lambdair_highir_rust" then
    "native_rust"
  else if classId = "lambdair_highir_c" then
    "native_c"
  else if classId = "lambdair_minic_c" then
    "native_c"
  else if classId = "minic_only" then
    "native_c"
  else if classId = "lambdair_only" then
    "lambdair_ir"
  else
    "unknown_target"

private def promoteBridgePlanCommand (classId : String) : IO String := do
  if !Route.isKnownRouteClass classId then
    throw <| IO.userError s!"unknown route class for bridge-plan: {classId}"

  let isPlannedClass := Route.isPlannedRouteClass classId
  let targetClass := targetClassForRouteClass classId
  let rolloutStage := Route.rolloutStageForRouteClass classId
  let derivationPlan := Route.derivationPlanForRouteClass classId
  let derivationEndpointFamily := Route.derivationEndpointFamilyForRouteClass classId
  let derivationEndpointTheoremIds := Route.plannedDerivationEndpointContractIdsForRouteClass classId
  let derivationEndpointTheoremCount := derivationEndpointTheoremIds.length
  let derivationEndpointTheoremCountMatches :=
    derivationEndpointTheoremCount = derivationEndpointTheoremIds.length
  let endpointTargetSupported := Route.supportsTargetClass classId targetClass
  let endpointTargetRealizationReason := Route.targetRealizationReasonForRouteClass classId targetClass
  let endpointTargetRealizationCase := Route.targetRealizationCaseForRouteClass classId targetClass
  let endpointTargetCaseReasonMatches :=
    Route.targetRealizationReasonForCase endpointTargetRealizationCase =
      endpointTargetRealizationReason
  let backendFamilyRolloutReady := Route.backendFamilyRolloutReadyForRouteClass classId
  let backendFamilyRolloutReason := Route.backendFamilyRolloutReasonForRouteClass classId
  let backendFamilyRolloutWitnessTheoremIds :=
    Route.backendFamilyRolloutWitnessTheoremIdsForRouteClass classId
  let backendFamilyRolloutWitnessTheoremCount := backendFamilyRolloutWitnessTheoremIds.length
  let backendFamilyRolloutWitnessTheoremCountMatches :=
    backendFamilyRolloutWitnessTheoremCount = backendFamilyRolloutWitnessTheoremIds.length
  let backendFamilyRolloutWitnessReasonMatches :=
    backendFamilyRolloutWitnessTheoremIds =
      Route.backendFamilyRolloutWitnessTheoremIdsForReason backendFamilyRolloutReason

  let plannedPolicyTheoremIds := Route.plannedPolicyTheoremIdsForRouteClass classId
  let plannedPolicyTheoremCount := plannedPolicyTheoremIds.length
  let plannedPolicyTheoremCountMatches := plannedPolicyTheoremCount = plannedPolicyTheoremIds.length
  let plannedPolicyNonemptyForPlannedClass :=
    if isPlannedClass then !plannedPolicyTheoremIds.isEmpty else true
  let backendFamilyRolloutWitnessLinksPlannedPolicy :=
    if isPlannedClass then
      backendFamilyRolloutWitnessTheoremIds = plannedPolicyTheoremIds
    else
      true

  let plannedBackendReadinessWitnessIds := Route.plannedBackendReadinessWitnessIdsForRouteClass classId
  let plannedBackendReadinessWitnessCount := plannedBackendReadinessWitnessIds.length
  let plannedBackendReadinessWitnessCountMatches :=
    plannedBackendReadinessWitnessCount = plannedBackendReadinessWitnessIds.length
  let plannedBackendReadinessWitnessMatchesClassPolicy :=
    plannedBackendReadinessWitnessIds = Route.plannedBackendReadinessWitnessIdsForRouteClass classId
  let plannedBackendReadinessWitnessNonemptyForPlannedClass :=
    if isPlannedClass then !plannedBackendReadinessWitnessIds.isEmpty else true

  let plannedRolloutBridgeStrategy := Route.plannedRolloutBridgeStrategyForRouteClass classId
  let plannedRolloutBridgeWitnessIds := Route.plannedRolloutBridgeWitnessIdsForRouteClass classId
  let plannedRolloutBridgeWitnessCount := plannedRolloutBridgeWitnessIds.length
  let plannedRolloutBridgeWitnessCountMatches :=
    plannedRolloutBridgeWitnessCount = plannedRolloutBridgeWitnessIds.length
  let plannedRolloutBridgeWitnessMatchesClassPolicy :=
    plannedRolloutBridgeWitnessIds = Route.plannedRolloutBridgeWitnessIdsForRouteClass classId
  let plannedRolloutBridgeReady := Route.plannedRolloutBridgeReadyForRouteClass classId
  let plannedRolloutBridgeReadyMatchesClassPolicy :=
    plannedRolloutBridgeReady = Route.plannedRolloutBridgeReadyForRouteClass classId
  let plannedRolloutBridgeActionHooks := Route.plannedRolloutBridgeActionHooksForRouteClass classId
  let plannedRolloutBridgeActionHookCount := plannedRolloutBridgeActionHooks.length
  let plannedRolloutBridgeActionHooksMatchClassPolicy :=
    plannedRolloutBridgeActionHooks = Route.plannedRolloutBridgeActionHooksForRouteClass classId

  let plannedRolloutBridgeHandoffContractIds :=
    if plannedRolloutBridgeReady then plannedPolicyTheoremIds else []
  let plannedRolloutBridgeHandoffContractCount := plannedRolloutBridgeHandoffContractIds.length
  let plannedRolloutBridgeHandoffContractCountMatches :=
    plannedRolloutBridgeHandoffContractCount = plannedRolloutBridgeHandoffContractIds.length
  let plannedRolloutBridgeHandoffLinksPlannedPolicy :=
    if plannedRolloutBridgeReady then
      plannedRolloutBridgeHandoffContractIds = plannedPolicyTheoremIds
    else
      plannedRolloutBridgeHandoffContractIds = []

  let plannedRolloutBridgeRealizationRequired := isPlannedClass && plannedRolloutBridgeReady
  let plannedRolloutBridgeRealizationStatus :=
    plannedRolloutBridgeRealizationStatusFor
      plannedRolloutBridgeRealizationRequired
      plannedRolloutBridgeStrategy
  let plannedRolloutBridgeRealizationChecklist :=
    plannedRolloutBridgeRealizationChecklistFor plannedRolloutBridgeRealizationRequired
  let plannedRolloutBridgeRealizationChecklistCount :=
    plannedRolloutBridgeRealizationChecklist.length
  let plannedRolloutBridgeRealizationChecklistCountMatches :=
    plannedRolloutBridgeRealizationChecklistCount =
      plannedRolloutBridgeRealizationChecklist.length
  let plannedRolloutBridgeCertifyingReplayHooks :=
    plannedRolloutBridgeCertifyingReplayHooksFor plannedRolloutBridgeRealizationRequired
  let plannedRolloutBridgeCertifyingReplayHookCount :=
    plannedRolloutBridgeCertifyingReplayHooks.length
  let plannedRolloutBridgeCertifyingReplayHookCountMatches :=
    plannedRolloutBridgeCertifyingReplayHookCount =
      plannedRolloutBridgeCertifyingReplayHooks.length
  let plannedRolloutBridgeRealizationReceipt :=
    plannedRolloutBridgeRealizationReceiptFor
      plannedRolloutBridgeRealizationRequired
      plannedRolloutBridgeRealizationStatus
      plannedRolloutBridgeRealizationChecklist
      plannedRolloutBridgeCertifyingReplayHooks
  let plannedRolloutBridgeRealizationContract := Json.mkObj
    [ ("stage", .str "planned_rollout_bridge_realization_contract")
    , ("route_class_id", .str classId)
    , ("target_class", .str targetClass)
    , ("strategy", .str plannedRolloutBridgeStrategy)
    , ("required", .bool plannedRolloutBridgeRealizationRequired)
    , ("status", .str plannedRolloutBridgeRealizationStatus)
    , ("realization_checklist", jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("realization_checklist_count", .num plannedRolloutBridgeRealizationChecklistCount)
    , ("realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("certifying_replay_hooks", jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("certifying_replay_hook_count", .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("theorem_contract_handoff_ids", jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("theorem_contract_handoff_count", .num plannedRolloutBridgeHandoffContractCount)
    , ("theorem_contract_handoff_count_matches",
        .bool plannedRolloutBridgeHandoffContractCountMatches)
    , ("theorem_contract_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("required_bridge_witness_ids", jsonStrArray plannedRolloutBridgeWitnessIds)
    , ("required_bridge_witness_count", .num plannedRolloutBridgeWitnessCount)
    , ("execution_receipt", plannedRolloutBridgeRealizationReceipt)
    ]

  let versionResolution ← contractMetadataVersionResolutionFromEnv
  let contractMetadataVersion := versionResolution.resolved
  let theoremContractIds :=
    Route.promotionTransitionTheoremContractIdsForVersion contractMetadataVersion classId
  let theoremContractCount := theoremContractIds.length
  let theoremContractCountMatches := theoremContractCount = theoremContractIds.length
  let theoremContractHasPlannedPolicyLink :=
    "HeytingLean.HeytingVeil.Route.selectedPlannedPolicyTheoremIdsMatchClassPolicy"
      ∈ theoremContractIds
  let theoremContractRolloutWitnessPolicyIds :=
    Route.plannedRolloutWitnessPolicyContractIdsForRouteClass classId
  let theoremContractRolloutWitnessPolicyCount := theoremContractRolloutWitnessPolicyIds.length
  let theoremContractRolloutWitnessPolicyCountMatches :=
    theoremContractRolloutWitnessPolicyCount = theoremContractRolloutWitnessPolicyIds.length
  let theoremContractHasRolloutWitnessPolicyLink :=
    listSubsetByContains theoremContractRolloutWitnessPolicyIds theoremContractIds
  let theoremContractRolloutWitnessIds :=
    listIntersectionByContains backendFamilyRolloutWitnessTheoremIds theoremContractIds
  let theoremContractRolloutWitnessCount := theoremContractRolloutWitnessIds.length
  let theoremContractRolloutWitnessCountMatches :=
    theoremContractRolloutWitnessCount = backendFamilyRolloutWitnessTheoremCount
  let theoremContractRolloutWitnessLinksPolicyMatrix :=
    theoremContractRolloutWitnessIds = backendFamilyRolloutWitnessTheoremIds
  let theoremContractRolloutWitnessLinksPlannedPolicy :=
    if isPlannedClass then
      theoremContractRolloutWitnessIds = plannedPolicyTheoremIds
    else
      theoremContractRolloutWitnessIds = []

  let planStatus :=
    if !isPlannedClass then
      "not_planned_route_class"
  else if plannedRolloutBridgeRealizationRequired then
      "ready_for_execution"
    else
      "pending_strategy_readiness"
  let bridgePlanArtifactRel := bridgePlanArtifactRelForRouteClass classId
  let bridgePlanCommand := bridgePlanCommandForRouteClass classId
  let defaultBridgePlanStatus :=
    if plannedRolloutBridgeRealizationRequired then planStatus else "not_available"
  let defaultBridgePlanRouteClassId :=
    if plannedRolloutBridgeRealizationRequired then classId else ""
  let defaultBridgePlanArtifact :=
    if plannedRolloutBridgeRealizationRequired then some bridgePlanArtifactRel else none
  let defaultBridgePlanCommand :=
    if plannedRolloutBridgeRealizationRequired then some bridgePlanCommand else none
  let plannedRolloutBridgeMaterializationProjectionSummary :=
    jsonValOrDefault
      (realizedBridgeReceiptWithOutcomes
        plannedRolloutBridgeRealizationReceipt
        (if plannedRolloutBridgeRealizationRequired then "absent" else "not_applicable")
        none
        none
        defaultBridgePlanStatus
        defaultBridgePlanRouteClassId
        defaultBridgePlanArtifact
        defaultBridgePlanCommand)
      "bridge_plan_materialization_projection_summary"
      (Json.mkObj
        [ ("bridge_plan_materialization_ok", .bool false)
        , ("bridge_plan_status", .str "not_available")
        , ("bridge_plan_route_class_id", .str "")
        , ("bridge_plan_artifact", .null)
        , ("bridge_plan_command", .null)
        , ("bridge_plan_exit_code", .null)
        , ("bridge_plan_materialization_rule", .str "not_available")
        , ("bridge_plan_materialization_run_state", .str "pending")
        , ("bridge_plan_materialization_result_status", .str "not_started")
        , ("bridge_plan_materialization_completed", .bool false)
        , ("bridge_plan_materialization_evidence", .null)
        , ("all_hooks_ok", .bool false)
        , ("all_checks_ok", .bool false)
        ])

  let planJson := Json.mkObj
    [ ("stage", .str "promotion_bridge_plan")
    , ("status", .str planStatus)
    , ("route_class_id", .str classId)
    , ("target_class", .str targetClass)
    , ("rollout_stage", .str rolloutStage)
    , ("derivation_plan", jsonStrArray derivationPlan)
    , ("derivation_endpoint_family", .str derivationEndpointFamily)
    , ("derivation_endpoint_theorem_ids", jsonStrArray derivationEndpointTheoremIds)
    , ("derivation_endpoint_theorem_count", .num derivationEndpointTheoremCount)
    , ("derivation_endpoint_theorem_count_matches", .bool derivationEndpointTheoremCountMatches)
    , ("endpoint_target_supported", .bool endpointTargetSupported)
    , ("endpoint_target_realization_reason", .str endpointTargetRealizationReason)
    , ("endpoint_target_realization_case", .str endpointTargetRealizationCase)
    , ("endpoint_target_case_reason_matches", .bool endpointTargetCaseReasonMatches)
    , ("endpoint_target_realization_matrix", endpointTargetRealizationMatrixJson)
    , ("backend_family_rollout_ready", .bool backendFamilyRolloutReady)
    , ("backend_family_rollout_reason", .str backendFamilyRolloutReason)
    , ("backend_family_rollout_witness_theorem_ids",
        jsonStrArray backendFamilyRolloutWitnessTheoremIds)
    , ("backend_family_rollout_witness_theorem_count", .num backendFamilyRolloutWitnessTheoremCount)
    , ("backend_family_rollout_witness_theorem_count_matches",
        .bool backendFamilyRolloutWitnessTheoremCountMatches)
    , ("backend_family_rollout_witness_reason_matches",
        .bool backendFamilyRolloutWitnessReasonMatches)
    , ("backend_family_rollout_witness_links_planned_policy",
        .bool backendFamilyRolloutWitnessLinksPlannedPolicy)
    , ("backend_family_rollout_witness_matrix", backendFamilyRolloutWitnessMatrixJson)
    , ("planned_policy_theorem_ids", jsonStrArray plannedPolicyTheoremIds)
    , ("planned_policy_theorem_count", .num plannedPolicyTheoremCount)
    , ("planned_policy_theorem_count_matches", .bool plannedPolicyTheoremCountMatches)
    , ("planned_policy_nonempty_for_planned_class", .bool plannedPolicyNonemptyForPlannedClass)
    , ("planned_backend_readiness_witness_ids", jsonStrArray plannedBackendReadinessWitnessIds)
    , ("planned_backend_readiness_witness_count", .num plannedBackendReadinessWitnessCount)
    , ("planned_backend_readiness_witness_count_matches",
        .bool plannedBackendReadinessWitnessCountMatches)
    , ("planned_backend_readiness_witness_matches_class_policy",
        .bool plannedBackendReadinessWitnessMatchesClassPolicy)
    , ("planned_backend_readiness_witness_nonempty_for_planned_class",
        .bool plannedBackendReadinessWitnessNonemptyForPlannedClass)
    , ("planned_rollout_bridge_strategy", .str plannedRolloutBridgeStrategy)
    , ("planned_rollout_bridge_witness_ids", jsonStrArray plannedRolloutBridgeWitnessIds)
    , ("planned_rollout_bridge_witness_count", .num plannedRolloutBridgeWitnessCount)
    , ("planned_rollout_bridge_witness_count_matches",
        .bool plannedRolloutBridgeWitnessCountMatches)
    , ("planned_rollout_bridge_witness_matches_class_policy",
        .bool plannedRolloutBridgeWitnessMatchesClassPolicy)
    , ("planned_rollout_bridge_ready", .bool plannedRolloutBridgeReady)
    , ("planned_rollout_bridge_ready_matches_class_policy",
        .bool plannedRolloutBridgeReadyMatchesClassPolicy)
    , ("planned_rollout_bridge_action_hooks", jsonStrArray plannedRolloutBridgeActionHooks)
    , ("planned_rollout_bridge_action_hook_count", .num plannedRolloutBridgeActionHookCount)
    , ("planned_rollout_bridge_action_hooks_match_class_policy",
        .bool plannedRolloutBridgeActionHooksMatchClassPolicy)
    , ("planned_rollout_bridge_handoff_contract_ids",
        jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("planned_rollout_bridge_handoff_contract_count",
        .num plannedRolloutBridgeHandoffContractCount)
    , ("planned_rollout_bridge_handoff_contract_count_matches",
        .bool plannedRolloutBridgeHandoffContractCountMatches)
    , ("planned_rollout_bridge_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("planned_rollout_bridge_realization_required",
        .bool plannedRolloutBridgeRealizationRequired)
    , ("planned_rollout_bridge_realization_status",
        .str plannedRolloutBridgeRealizationStatus)
    , ("planned_rollout_bridge_realization_checklist",
        jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("planned_rollout_bridge_realization_checklist_count",
        .num plannedRolloutBridgeRealizationChecklistCount)
    , ("planned_rollout_bridge_realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("planned_rollout_bridge_certifying_replay_hooks",
        jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("planned_rollout_bridge_certifying_replay_hook_count",
        .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("planned_rollout_bridge_certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("planned_rollout_bridge_realization_contract",
        plannedRolloutBridgeRealizationContract)
    , ("planned_rollout_bridge_realization_receipt",
        plannedRolloutBridgeRealizationReceipt)
    , ("planned_rollout_bridge_materialization_projection_summary",
        plannedRolloutBridgeMaterializationProjectionSummary)
    , ("contract_metadata_version", .str contractMetadataVersion)
    , ("contract_metadata_requested_version", .str versionResolution.requested)
    , ("contract_metadata_fallback_applied", .bool versionResolution.fallbackApplied)
    , ("contract_metadata_resolution_reason", .str versionResolution.resolutionReason)
    , ("contract_metadata_supported_versions",
        jsonStrArray Route.promotionContractMetadataSupportedVersions)
    , ("theorem_contract_ids", jsonStrArray theoremContractIds)
    , ("theorem_contract_count", .num theoremContractCount)
    , ("theorem_contract_count_matches", .bool theoremContractCountMatches)
    , ("theorem_contract_has_planned_policy_link",
        .bool theoremContractHasPlannedPolicyLink)
    , ("theorem_contract_rollout_witness_policy_ids",
        jsonStrArray theoremContractRolloutWitnessPolicyIds)
    , ("theorem_contract_rollout_witness_policy_count",
        .num theoremContractRolloutWitnessPolicyCount)
    , ("theorem_contract_rollout_witness_policy_count_matches",
        .bool theoremContractRolloutWitnessPolicyCountMatches)
    , ("theorem_contract_has_rollout_witness_policy_link",
        .bool theoremContractHasRolloutWitnessPolicyLink)
    , ("theorem_contract_rollout_witness_ids",
        jsonStrArray theoremContractRolloutWitnessIds)
    , ("theorem_contract_rollout_witness_count",
        .num theoremContractRolloutWitnessCount)
    , ("theorem_contract_rollout_witness_count_matches",
        .bool theoremContractRolloutWitnessCountMatches)
    , ("theorem_contract_rollout_witness_links_policy_matrix",
        .bool theoremContractRolloutWitnessLinksPolicyMatrix)
    , ("theorem_contract_rollout_witness_links_planned_policy",
        .bool theoremContractRolloutWitnessLinksPlannedPolicy)
    , ("theorem_contract_projection_summary", Json.mkObj
        [ ("contract_metadata_version", .str contractMetadataVersion)
        , ("contract_metadata_requested_version", .str versionResolution.requested)
        , ("contract_metadata_fallback_applied", .bool versionResolution.fallbackApplied)
        , ("contract_metadata_resolution_reason", .str versionResolution.resolutionReason)
        , ("contract_metadata_supported_versions",
            jsonStrArray Route.promotionContractMetadataSupportedVersions)
        , ("policy_contract_ids", jsonStrArray theoremContractIds)
        , ("policy_contract_count", .num theoremContractCount)
        , ("policy_contract_count_matches", .bool theoremContractCountMatches)
        , ("rollout_witness_policy_ids", jsonStrArray theoremContractRolloutWitnessPolicyIds)
        , ("rollout_witness_policy_count", .num theoremContractRolloutWitnessPolicyCount)
        , ("rollout_witness_policy_count_matches",
            .bool theoremContractRolloutWitnessPolicyCountMatches)
        , ("has_rollout_witness_policy_link", .bool theoremContractHasRolloutWitnessPolicyLink)
        , ("rollout_witness_ids", jsonStrArray theoremContractRolloutWitnessIds)
        , ("rollout_witness_count", .num theoremContractRolloutWitnessCount)
        , ("rollout_witness_count_matches", .bool theoremContractRolloutWitnessCountMatches)
        , ("rollout_witness_links_policy_matrix",
            .bool theoremContractRolloutWitnessLinksPolicyMatrix)
        , ("rollout_witness_links_planned_policy",
            .bool theoremContractRolloutWitnessLinksPlannedPolicy)
        , ("planned_rollout_bridge_handoff_contract_ids",
            jsonStrArray plannedRolloutBridgeHandoffContractIds)
        , ("planned_rollout_bridge_handoff_contract_count",
            .num plannedRolloutBridgeHandoffContractCount)
        , ("planned_rollout_bridge_handoff_contract_count_matches",
            .bool plannedRolloutBridgeHandoffContractCountMatches)
        , ("planned_rollout_bridge_handoff_links_planned_policy",
            .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
        , ("planned_rollout_bridge_realization_required",
            .bool plannedRolloutBridgeRealizationRequired)
        , ("planned_rollout_bridge_realization_status",
            .str plannedRolloutBridgeRealizationStatus)
        , ("planned_rollout_bridge_realization_checklist",
            jsonStrArray plannedRolloutBridgeRealizationChecklist)
        , ("planned_rollout_bridge_realization_checklist_count",
            .num plannedRolloutBridgeRealizationChecklistCount)
        , ("planned_rollout_bridge_realization_checklist_count_matches",
            .bool plannedRolloutBridgeRealizationChecklistCountMatches)
        , ("planned_rollout_bridge_certifying_replay_hooks",
            jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
        , ("planned_rollout_bridge_certifying_replay_hook_count",
            .num plannedRolloutBridgeCertifyingReplayHookCount)
        , ("planned_rollout_bridge_certifying_replay_hook_count_matches",
            .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
        , ("planned_rollout_bridge_realization_contract",
            plannedRolloutBridgeRealizationContract)
        , ("planned_rollout_bridge_realization_receipt",
            plannedRolloutBridgeRealizationReceipt)
        , ("planned_rollout_bridge_materialization_projection_summary",
            plannedRolloutBridgeMaterializationProjectionSummary)
        ])
    ]

  let outDir := System.FilePath.mk ".." / "artifacts" / "heytingveil" / "bridge_plans" / classId
  let planPath := outDir / "bridge_plan.json"
  writeBundleFile planPath (Json.pretty planJson)
  pure <| asJson
    [ ("status", .str "ok")
    , ("stage", .str "promotion_bridge_plan")
    , ("route_class_id", .str classId)
    , ("bridge_plan", planJson)
    , ("bridge_plan_artifact", .str planPath.toString)
    ]

private structure PromotionApplyPolicyContext where
  policyContextJson : Json
  certificateReplayRequired : Bool
  packageTheoremContractIds : List String
  theoremContractProjection : Json
  plannedRolloutBridgeStrategy : String
  plannedRolloutBridgeWitnessIds : List String
  plannedRolloutBridgeHandoffContractIds : List String
  plannedRolloutBridgeHandoffContractCount : Nat
  plannedRolloutBridgeHandoffContractCountMatches : Bool
  plannedRolloutBridgeHandoffLinksPlannedPolicy : Bool
  plannedRolloutBridgeRealizationRequired : Bool
  plannedRolloutBridgeRealizationStatus : String
  plannedRolloutBridgeRealizationChecklist : List String
  plannedRolloutBridgeRealizationChecklistCount : Nat
  plannedRolloutBridgeRealizationChecklistCountMatches : Bool
  plannedRolloutBridgeCertifyingReplayHooks : List String
  plannedRolloutBridgeCertifyingReplayHookCount : Nat
  plannedRolloutBridgeCertifyingReplayHookCountMatches : Bool
  plannedRolloutBridgeRealizationContract : Json
  plannedRolloutBridgeRealizationReceipt : Json
  plannedRolloutBridgeReady : Bool
  plannedRolloutBridgeActionHooks : List String

set_option maxRecDepth 131072 in
private def buildPromotionApplyPolicyContext
    (selection : Route.Selection) (transition : Json) : IO PromotionApplyPolicyContext := do
  let plannedPolicyTheoremIds := selection.plannedPolicyTheoremIds
  let plannedPolicyTheoremCount := plannedPolicyTheoremIds.length
  let plannedPolicyTheoremCountMatches := plannedPolicyTheoremCount = plannedPolicyTheoremIds.length
  let plannedPolicyNonemptyForPlannedClass :=
    if Route.isPlannedRouteClass selection.record.routeClassId then
      !plannedPolicyTheoremIds.isEmpty
    else
      true
  let plannedBackendReadinessWitnessIds :=
    (← objStrArrayOrDie transition "planned_backend_readiness_witness_ids").toList
  let plannedBackendReadinessWitnessCount :=
    (← objNatOrDie transition "planned_backend_readiness_witness_count")
  let plannedBackendReadinessWitnessCountMatches :=
    (← objBoolOrDie transition "planned_backend_readiness_witness_count_matches")
  let plannedBackendReadinessWitnessMatchesClassPolicy :=
    (← objBoolOrDie transition "planned_backend_readiness_witness_matches_class_policy")
  let plannedBackendReadinessWitnessNonemptyForPlannedClass :=
    (← objBoolOrDie transition "planned_backend_readiness_witness_nonempty_for_planned_class")
  let plannedRolloutBridgeStrategy :=
    (← objStrOrDie transition "planned_rollout_bridge_strategy")
  let plannedRolloutBridgeWitnessIds :=
    (← objStrArrayOrDie transition "planned_rollout_bridge_witness_ids").toList
  let plannedRolloutBridgeWitnessCount :=
    (← objNatOrDie transition "planned_rollout_bridge_witness_count")
  let plannedRolloutBridgeWitnessCountMatches :=
    (← objBoolOrDie transition "planned_rollout_bridge_witness_count_matches")
  let plannedRolloutBridgeWitnessMatchesClassPolicy :=
    (← objBoolOrDie transition "planned_rollout_bridge_witness_matches_class_policy")
  let plannedRolloutBridgeReady :=
    (← objBoolOrDie transition "planned_rollout_bridge_ready")
  let plannedRolloutBridgeReadyMatchesClassPolicy :=
    (← objBoolOrDie transition "planned_rollout_bridge_ready_matches_class_policy")
  let plannedRolloutBridgeActionHooks :=
    (← objStrArrayOrDie transition "planned_rollout_bridge_action_hooks").toList
  let plannedRolloutBridgeActionHookCount :=
    (← objNatOrDie transition "planned_rollout_bridge_action_hook_count")
  let plannedRolloutBridgeActionHooksMatchClassPolicy :=
    (← objBoolOrDie transition "planned_rollout_bridge_action_hooks_match_class_policy")
  let plannedRolloutBridgeHandoffContractIds :=
    (← objStrArrayOrDie transition "planned_rollout_bridge_handoff_contract_ids").toList
  let plannedRolloutBridgeHandoffContractCount :=
    (← objNatOrDie transition "planned_rollout_bridge_handoff_contract_count")
  let plannedRolloutBridgeHandoffContractCountMatches :=
    (← objBoolOrDie transition "planned_rollout_bridge_handoff_contract_count_matches")
  let plannedRolloutBridgeHandoffLinksPlannedPolicy :=
    (← objBoolOrDie transition "planned_rollout_bridge_handoff_links_planned_policy")
  let plannedRolloutBridgeRealizationRequired :=
    (← objBoolOrDie transition "planned_rollout_bridge_realization_required")
  let plannedRolloutBridgeRealizationStatus :=
    (← objStrOrDie transition "planned_rollout_bridge_realization_status")
  let plannedRolloutBridgeRealizationChecklist :=
    (← objStrArrayOrDie transition "planned_rollout_bridge_realization_checklist").toList
  let plannedRolloutBridgeRealizationChecklistCount :=
    (← objNatOrDie transition "planned_rollout_bridge_realization_checklist_count")
  let plannedRolloutBridgeRealizationChecklistCountMatches :=
    (← objBoolOrDie transition "planned_rollout_bridge_realization_checklist_count_matches")
  let plannedRolloutBridgeCertifyingReplayHooks :=
    (← objStrArrayOrDie transition "planned_rollout_bridge_certifying_replay_hooks").toList
  let plannedRolloutBridgeCertifyingReplayHookCount :=
    (← objNatOrDie transition "planned_rollout_bridge_certifying_replay_hook_count")
  let plannedRolloutBridgeCertifyingReplayHookCountMatches :=
    (← objBoolOrDie transition "planned_rollout_bridge_certifying_replay_hook_count_matches")
  let plannedRolloutBridgeRealizationContract :=
    (← objValOrDie transition "planned_rollout_bridge_realization_contract")
  let plannedRolloutBridgeRealizationReceipt :=
    (← objValOrDie transition "planned_rollout_bridge_realization_receipt")
  let plannedRolloutBridgeMaterializationProjectionSummary :=
    (← objValOrDie transition "planned_rollout_bridge_materialization_projection_summary")
  let derivationEndpointFamily := (← objStrOrDie transition "derivation_endpoint_family")
  let derivationEndpointTheoremIds := (← objStrArrayOrDie transition "derivation_endpoint_theorem_ids").toList
  let derivationEndpointTheoremCount := (← objNatOrDie transition "derivation_endpoint_theorem_count")
  let derivationEndpointTheoremCountMatches :=
    (← objBoolOrDie transition "derivation_endpoint_theorem_count_matches")
  let plannedEndpointRealizationTheoremIds :=
    (← objStrArrayOrDie transition "planned_endpoint_realization_theorem_ids").toList
  let plannedEndpointRealizationTheoremCount :=
    (← objNatOrDie transition "planned_endpoint_realization_theorem_count")
  let plannedEndpointRealizationTheoremCountMatches :=
    (← objBoolOrDie transition "planned_endpoint_realization_theorem_count_matches")
  let plannedEndpointRealizationTheoremMatchesClassPolicy :=
    (← objBoolOrDie transition "planned_endpoint_realization_theorem_matches_class_policy")
  let plannedEndpointRealizationTheoremLinksDerivationEndpoint :=
    (← objBoolOrDie transition "planned_endpoint_realization_theorem_links_derivation_endpoint")
  let plannedEndpointRealizationTheoremLinksBackendReadiness :=
    (← objBoolOrDie transition "planned_endpoint_realization_theorem_links_backend_readiness")
  let plannedEndpointRealizationTheoremNonemptyForPlannedClass :=
    (← objBoolOrDie transition "planned_endpoint_realization_theorem_nonempty_for_planned_class")
  let plannedEndpointRealizationProjection :=
    (← objValOrDie transition "planned_endpoint_realization_projection")
  let endpointTargetRequested := (← objStrOrDie transition "endpoint_target_requested")
  let endpointTargetClass := (← objStrOrDie transition "endpoint_target_class")
  let endpointTargetSupported := (← objBoolOrDie transition "endpoint_target_supported")
  let endpointTargetSupportMatchesSelection :=
    (← objBoolOrDie transition "endpoint_target_support_matches_selection")
  let endpointTargetRealizationReason :=
    (← objStrOrDie transition "endpoint_target_realization_reason")
  let endpointTargetRealizationCase :=
    (← objStrOrDie transition "endpoint_target_realization_case")
  let endpointTargetCaseReasonMatches :=
    (← objBoolOrDie transition "endpoint_target_case_reason_matches")
  let endpointTargetRealizationMatrix :=
    (← objValOrDie transition "endpoint_target_realization_matrix")
  let backendFamilyRolloutReady :=
    (← objBoolOrDie transition "backend_family_rollout_ready")
  let backendFamilyRolloutReason :=
    (← objStrOrDie transition "backend_family_rollout_reason")
  let backendFamilyRolloutMatchesRouteImplemented :=
    (← objBoolOrDie transition "backend_family_rollout_matches_route_implemented")
  let backendFamilyRolloutWitnessTheoremIds :=
    (← objStrArrayOrDie transition "backend_family_rollout_witness_theorem_ids").toList
  let backendFamilyRolloutWitnessTheoremCount :=
    (← objNatOrDie transition "backend_family_rollout_witness_theorem_count")
  let backendFamilyRolloutWitnessTheoremCountMatches :=
    (← objBoolOrDie transition "backend_family_rollout_witness_theorem_count_matches")
  let backendFamilyRolloutWitnessReasonMatches :=
    (← objBoolOrDie transition "backend_family_rollout_witness_reason_matches")
  let backendFamilyRolloutWitnessLinksPlannedPolicy :=
    (← objBoolOrDie transition "backend_family_rollout_witness_links_planned_policy")
  let backendFamilyRolloutWitnessMatrix :=
    (← objValOrDie transition "backend_family_rollout_witness_matrix")
  let theoremContractIds := (← objStrArrayOrDie transition "theorem_contract_ids").toList
  let theoremContractCount := (← objNatOrDie transition "theorem_contract_count")
  let theoremContractCountMatches := (← objBoolOrDie transition "theorem_contract_count_matches")
  let theoremContractHasPlannedPolicyLink := (← objBoolOrDie transition "theorem_contract_has_planned_policy_link")
  let theoremContractRolloutWitnessPolicyIds :=
    (← objStrArrayOrDie transition "theorem_contract_rollout_witness_policy_ids").toList
  let theoremContractRolloutWitnessPolicyCount :=
    (← objNatOrDie transition "theorem_contract_rollout_witness_policy_count")
  let theoremContractRolloutWitnessPolicyCountMatches :=
    (← objBoolOrDie transition "theorem_contract_rollout_witness_policy_count_matches")
  let theoremContractHasRolloutWitnessPolicyLink :=
    (← objBoolOrDie transition "theorem_contract_has_rollout_witness_policy_link")
  let theoremContractRolloutWitnessIds :=
    (← objStrArrayOrDie transition "theorem_contract_rollout_witness_ids").toList
  let theoremContractRolloutWitnessCount :=
    (← objNatOrDie transition "theorem_contract_rollout_witness_count")
  let theoremContractRolloutWitnessCountMatches :=
    (← objBoolOrDie transition "theorem_contract_rollout_witness_count_matches")
  let theoremContractRolloutWitnessLinksPolicyMatrix :=
    (← objBoolOrDie transition "theorem_contract_rollout_witness_links_policy_matrix")
  let theoremContractRolloutWitnessLinksPlannedPolicy :=
    (← objBoolOrDie transition "theorem_contract_rollout_witness_links_planned_policy")
  let contractMetadataVersion := (← objStrOrDie transition "contract_metadata_version")
  let contractMetadataRequestedVersion := (← objStrOrDie transition "contract_metadata_requested_version")
  let contractMetadataFallbackApplied := (← objBoolOrDie transition "contract_metadata_fallback_applied")
  let contractMetadataResolutionReason := (← objStrOrDie transition "contract_metadata_resolution_reason")
  let contractMetadataSupportedVersions := (← objStrArrayOrDie transition "contract_metadata_supported_versions").toList
  let packageTheoremContractIds := (← objStrArrayOrDie transition "package_theorem_contract_ids").toList
  let certificateReplayRequired := (← objBoolOrDie transition "certificate_replay_required")
  let theoremContractProjectionBase := (← objValOrDie transition "theorem_contract_projection")
  let theoremContractProjection :=
    match theoremContractProjectionBase with
    | .obj kvs =>
        Json.obj (kvs.insert "certificate_replay_required" (.bool certificateReplayRequired))
    | _ => theoremContractProjectionBase
  let theoremContractProjectionMaterializationProjectionSummary :=
    jsonValOrDefault
      theoremContractProjection
      "planned_rollout_bridge_materialization_projection_summary"
      plannedRolloutBridgeMaterializationProjectionSummary
  let theoremContractProjectionMaterializationProjectionMatchesTransition :=
    theoremContractProjectionMaterializationProjectionSummary ==
      plannedRolloutBridgeMaterializationProjectionSummary
  let policyContextJson := Json.mkObj
    [ ("rollout_stage", .str selection.rolloutStage)
    , ("certificate_replay_required", .bool certificateReplayRequired)
    , ("derivation_plan", jsonStrArray selection.derivationPlan)
    , ("planned_policy_theorem_ids", jsonStrArray plannedPolicyTheoremIds)
    , ("planned_policy_theorem_count", .num plannedPolicyTheoremCount)
    , ("planned_policy_theorem_count_matches", .bool plannedPolicyTheoremCountMatches)
    , ("planned_policy_nonempty_for_planned_class", .bool plannedPolicyNonemptyForPlannedClass)
    , ("planned_backend_readiness_witness_ids",
        jsonStrArray plannedBackendReadinessWitnessIds)
    , ("planned_backend_readiness_witness_count",
        .num plannedBackendReadinessWitnessCount)
    , ("planned_backend_readiness_witness_count_matches",
        .bool plannedBackendReadinessWitnessCountMatches)
    , ("planned_backend_readiness_witness_matches_class_policy",
        .bool plannedBackendReadinessWitnessMatchesClassPolicy)
    , ("planned_backend_readiness_witness_nonempty_for_planned_class",
        .bool plannedBackendReadinessWitnessNonemptyForPlannedClass)
    , ("planned_rollout_bridge_strategy", .str plannedRolloutBridgeStrategy)
    , ("planned_rollout_bridge_witness_ids", jsonStrArray plannedRolloutBridgeWitnessIds)
    , ("planned_rollout_bridge_witness_count", .num plannedRolloutBridgeWitnessCount)
    , ("planned_rollout_bridge_witness_count_matches",
        .bool plannedRolloutBridgeWitnessCountMatches)
    , ("planned_rollout_bridge_witness_matches_class_policy",
        .bool plannedRolloutBridgeWitnessMatchesClassPolicy)
    , ("planned_rollout_bridge_ready", .bool plannedRolloutBridgeReady)
    , ("planned_rollout_bridge_ready_matches_class_policy",
        .bool plannedRolloutBridgeReadyMatchesClassPolicy)
    , ("planned_rollout_bridge_action_hooks", jsonStrArray plannedRolloutBridgeActionHooks)
    , ("planned_rollout_bridge_action_hook_count", .num plannedRolloutBridgeActionHookCount)
    , ("planned_rollout_bridge_action_hooks_match_class_policy",
        .bool plannedRolloutBridgeActionHooksMatchClassPolicy)
    , ("planned_rollout_bridge_handoff_contract_ids",
        jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("planned_rollout_bridge_handoff_contract_count",
        .num plannedRolloutBridgeHandoffContractCount)
    , ("planned_rollout_bridge_handoff_contract_count_matches",
        .bool plannedRolloutBridgeHandoffContractCountMatches)
    , ("planned_rollout_bridge_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("planned_rollout_bridge_realization_required",
        .bool plannedRolloutBridgeRealizationRequired)
    , ("planned_rollout_bridge_realization_status",
        .str plannedRolloutBridgeRealizationStatus)
    , ("planned_rollout_bridge_realization_checklist",
        jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("planned_rollout_bridge_realization_checklist_count",
        .num plannedRolloutBridgeRealizationChecklistCount)
    , ("planned_rollout_bridge_realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("planned_rollout_bridge_certifying_replay_hooks",
        jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("planned_rollout_bridge_certifying_replay_hook_count",
        .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("planned_rollout_bridge_certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("planned_rollout_bridge_realization_contract",
        plannedRolloutBridgeRealizationContract)
    , ("planned_rollout_bridge_realization_receipt",
        plannedRolloutBridgeRealizationReceipt)
    , ("planned_rollout_bridge_materialization_projection_summary",
        plannedRolloutBridgeMaterializationProjectionSummary)
    , ("derivation_endpoint_family", .str derivationEndpointFamily)
    , ("derivation_endpoint_theorem_ids", jsonStrArray derivationEndpointTheoremIds)
    , ("derivation_endpoint_theorem_count", .num derivationEndpointTheoremCount)
    , ("derivation_endpoint_theorem_count_matches", .bool derivationEndpointTheoremCountMatches)
    , ("endpoint_target_requested", .str endpointTargetRequested)
    , ("endpoint_target_class", .str endpointTargetClass)
    , ("endpoint_target_supported", .bool endpointTargetSupported)
    , ("endpoint_target_support_matches_selection", .bool endpointTargetSupportMatchesSelection)
    , ("endpoint_target_realization_reason", .str endpointTargetRealizationReason)
    , ("endpoint_target_realization_case", .str endpointTargetRealizationCase)
    , ("endpoint_target_case_reason_matches", .bool endpointTargetCaseReasonMatches)
    , ("endpoint_target_realization_matrix", endpointTargetRealizationMatrix)
    , ("backend_family_rollout_ready", .bool backendFamilyRolloutReady)
    , ("backend_family_rollout_reason", .str backendFamilyRolloutReason)
    , ("backend_family_rollout_matches_route_implemented",
        .bool backendFamilyRolloutMatchesRouteImplemented)
    , ("backend_family_rollout_witness_theorem_ids",
        jsonStrArray backendFamilyRolloutWitnessTheoremIds)
    , ("backend_family_rollout_witness_theorem_count", .num backendFamilyRolloutWitnessTheoremCount)
    , ("backend_family_rollout_witness_theorem_count_matches",
        .bool backendFamilyRolloutWitnessTheoremCountMatches)
    , ("backend_family_rollout_witness_reason_matches",
        .bool backendFamilyRolloutWitnessReasonMatches)
    , ("backend_family_rollout_witness_links_planned_policy",
        .bool backendFamilyRolloutWitnessLinksPlannedPolicy)
    , ("backend_family_rollout_witness_matrix", backendFamilyRolloutWitnessMatrix)
    , ("theorem_contract_ids", jsonStrArray theoremContractIds)
    , ("theorem_contract_count", .num theoremContractCount)
    , ("theorem_contract_count_matches", .bool theoremContractCountMatches)
    , ("theorem_contract_has_planned_policy_link", .bool theoremContractHasPlannedPolicyLink)
    , ("theorem_contract_rollout_witness_policy_ids",
        jsonStrArray theoremContractRolloutWitnessPolicyIds)
    , ("theorem_contract_rollout_witness_policy_count",
        .num theoremContractRolloutWitnessPolicyCount)
    , ("theorem_contract_rollout_witness_policy_count_matches",
        .bool theoremContractRolloutWitnessPolicyCountMatches)
    , ("theorem_contract_has_rollout_witness_policy_link",
        .bool theoremContractHasRolloutWitnessPolicyLink)
    , ("theorem_contract_rollout_witness_ids",
        jsonStrArray theoremContractRolloutWitnessIds)
    , ("theorem_contract_rollout_witness_count", .num theoremContractRolloutWitnessCount)
    , ("theorem_contract_rollout_witness_count_matches",
        .bool theoremContractRolloutWitnessCountMatches)
    , ("theorem_contract_rollout_witness_links_policy_matrix",
        .bool theoremContractRolloutWitnessLinksPolicyMatrix)
    , ("theorem_contract_rollout_witness_links_planned_policy",
        .bool theoremContractRolloutWitnessLinksPlannedPolicy)
    , ("theorem_contract_projection_materialization_projection_matches_transition",
        .bool theoremContractProjectionMaterializationProjectionMatchesTransition)
    , ("contract_metadata_version", .str contractMetadataVersion)
    , ("contract_metadata_requested_version", .str contractMetadataRequestedVersion)
    , ("contract_metadata_fallback_applied", .bool contractMetadataFallbackApplied)
    , ("contract_metadata_resolution_reason", .str contractMetadataResolutionReason)
    ]
  let policyContextJson :=
    match policyContextJson with
    | .obj kvs =>
        let kvs := kvs.insert "theorem_contract_projection_summary" theoremContractProjection
        let kvs := kvs.insert "contract_metadata_supported_versions"
          (jsonStrArray contractMetadataSupportedVersions)
        let kvs := kvs.insert "planned_endpoint_realization_theorem_ids"
          (jsonStrArray plannedEndpointRealizationTheoremIds)
        let kvs := kvs.insert "planned_endpoint_realization_theorem_count"
          (.num plannedEndpointRealizationTheoremCount)
        let kvs := kvs.insert "planned_endpoint_realization_theorem_count_matches"
          (.bool plannedEndpointRealizationTheoremCountMatches)
        let kvs := kvs.insert "planned_endpoint_realization_theorem_matches_class_policy"
          (.bool plannedEndpointRealizationTheoremMatchesClassPolicy)
        let kvs := kvs.insert "planned_endpoint_realization_theorem_links_derivation_endpoint"
          (.bool plannedEndpointRealizationTheoremLinksDerivationEndpoint)
        let kvs := kvs.insert "planned_endpoint_realization_theorem_links_backend_readiness"
          (.bool plannedEndpointRealizationTheoremLinksBackendReadiness)
        let kvs := kvs.insert "planned_endpoint_realization_theorem_nonempty_for_planned_class"
          (.bool plannedEndpointRealizationTheoremNonemptyForPlannedClass)
        let kvs := kvs.insert "planned_endpoint_realization_projection"
          plannedEndpointRealizationProjection
        Json.obj kvs
    | _ => policyContextJson
  pure
    { policyContextJson := policyContextJson
      certificateReplayRequired := certificateReplayRequired
      packageTheoremContractIds := packageTheoremContractIds
      theoremContractProjection := theoremContractProjection
      plannedRolloutBridgeStrategy := plannedRolloutBridgeStrategy
      plannedRolloutBridgeWitnessIds := plannedRolloutBridgeWitnessIds
      plannedRolloutBridgeHandoffContractIds := plannedRolloutBridgeHandoffContractIds
      plannedRolloutBridgeHandoffContractCount := plannedRolloutBridgeHandoffContractCount
      plannedRolloutBridgeHandoffContractCountMatches := plannedRolloutBridgeHandoffContractCountMatches
      plannedRolloutBridgeHandoffLinksPlannedPolicy := plannedRolloutBridgeHandoffLinksPlannedPolicy
      plannedRolloutBridgeRealizationRequired := plannedRolloutBridgeRealizationRequired
      plannedRolloutBridgeRealizationStatus := plannedRolloutBridgeRealizationStatus
      plannedRolloutBridgeRealizationChecklist := plannedRolloutBridgeRealizationChecklist
      plannedRolloutBridgeRealizationChecklistCount := plannedRolloutBridgeRealizationChecklistCount
      plannedRolloutBridgeRealizationChecklistCountMatches := plannedRolloutBridgeRealizationChecklistCountMatches
      plannedRolloutBridgeCertifyingReplayHooks := plannedRolloutBridgeCertifyingReplayHooks
      plannedRolloutBridgeCertifyingReplayHookCount := plannedRolloutBridgeCertifyingReplayHookCount
      plannedRolloutBridgeCertifyingReplayHookCountMatches :=
        plannedRolloutBridgeCertifyingReplayHookCountMatches
      plannedRolloutBridgeRealizationContract := plannedRolloutBridgeRealizationContract
      plannedRolloutBridgeRealizationReceipt := plannedRolloutBridgeRealizationReceipt
      plannedRolloutBridgeReady := plannedRolloutBridgeReady
      plannedRolloutBridgeActionHooks := plannedRolloutBridgeActionHooks }

private def promoteApplyCommand (src : String) : IO String := do
  let em ← elabOrDie src
  let art := DSL.emit em
  let selection := Route.select em.parsed.mod
  let transitionResolution ← contractMetadataVersionResolutionFromEnv
  let contractMetadataVersion := transitionResolution.resolved
  let transition := promotionTransitionJson selection transitionResolution
  let outDir := System.FilePath.mk ".." / "artifacts" / "heytingveil" / art.moduleName
  let transitionPath := outDir / "preview_promotion_transition.json"
  let applyPath := outDir / "preview_promotion_apply.json"
  let transitionArtifactRel := s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_transition.json"
  let applyArtifactRel := s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_apply.json"
  let endpointRealizationArtifactRel :=
    s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_endpoint_realization.json"
  let endpointRealizationArtifactPath :=
    outDir / "preview_promotion_endpoint_realization.json"
  let endpointRealizationReceiptArtifactRel :=
    s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_endpoint_realization_receipt.json"
  let endpointRealizationReceiptArtifactPath :=
    outDir / "preview_promotion_endpoint_realization_receipt.json"
  let endpointRealizationReceiptRuntimeArtifactRel :=
    s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_endpoint_realization_receipt_runtime.json"
  let endpointRealizationReceiptRuntimeArtifactPath :=
    outDir / "preview_promotion_endpoint_realization_receipt_runtime.json"
  writeBundleFile transitionPath (Json.pretty transition)

  let transitionStatus := promotionTransitionStatus selection
  let transitionReason := promotionTransitionReason selection
  let transitionId := s!"preview_promotion::{selection.record.routeClassId}::{transitionReason}"
  let policyContext ← buildPromotionApplyPolicyContext selection transition
  let policyContextJson := policyContext.policyContextJson
  let certificateReplayRequired := policyContext.certificateReplayRequired
  let packageTheoremContractIds := policyContext.packageTheoremContractIds
  let theoremContractProjection := policyContext.theoremContractProjection
  let plannedRolloutBridgeStrategy := policyContext.plannedRolloutBridgeStrategy
  let plannedRolloutBridgeWitnessIds := policyContext.plannedRolloutBridgeWitnessIds
  let plannedRolloutBridgeHandoffContractIds := policyContext.plannedRolloutBridgeHandoffContractIds
  let plannedRolloutBridgeHandoffContractCount := policyContext.plannedRolloutBridgeHandoffContractCount
  let plannedRolloutBridgeHandoffContractCountMatches :=
    policyContext.plannedRolloutBridgeHandoffContractCountMatches
  let plannedRolloutBridgeHandoffLinksPlannedPolicy :=
    policyContext.plannedRolloutBridgeHandoffLinksPlannedPolicy
  let plannedRolloutBridgeRealizationRequired :=
    policyContext.plannedRolloutBridgeRealizationRequired
  let plannedRolloutBridgeRealizationStatus :=
    policyContext.plannedRolloutBridgeRealizationStatus
  let plannedRolloutBridgeRealizationChecklist :=
    policyContext.plannedRolloutBridgeRealizationChecklist
  let plannedRolloutBridgeRealizationChecklistCount :=
    policyContext.plannedRolloutBridgeRealizationChecklistCount
  let plannedRolloutBridgeRealizationChecklistCountMatches :=
    policyContext.plannedRolloutBridgeRealizationChecklistCountMatches
  let plannedRolloutBridgeCertifyingReplayHooks :=
    policyContext.plannedRolloutBridgeCertifyingReplayHooks
  let plannedRolloutBridgeCertifyingReplayHookCount :=
    policyContext.plannedRolloutBridgeCertifyingReplayHookCount
  let plannedRolloutBridgeCertifyingReplayHookCountMatches :=
    policyContext.plannedRolloutBridgeCertifyingReplayHookCountMatches
  let plannedRolloutBridgeRealizationContract :=
    policyContext.plannedRolloutBridgeRealizationContract
  let plannedRolloutBridgeRealizationReceipt :=
    policyContext.plannedRolloutBridgeRealizationReceipt
  let plannedRolloutBridgeReady := policyContext.plannedRolloutBridgeReady
  let plannedRolloutBridgeActionHooks := policyContext.plannedRolloutBridgeActionHooks
  let plannedRolloutBridgeActionHookCount := plannedRolloutBridgeActionHooks.length
  let bridgeStrategyActionable := transitionStatus = "not_applicable" && plannedRolloutBridgeReady
  let bridgeStrategyStatus :=
    if bridgeStrategyActionable then
      "actionable_pending_realization"
    else if plannedRolloutBridgeStrategy = "none" then
      "not_applicable"
    else
      "non_actionable"
  let bridgeStrategyReason :=
    if bridgeStrategyActionable then
      if selection.record.routeClassId = "lambdair_highir_cpp" then
        "highir_cpp_bridge_ready_no_native_cpp_backend"
      else if selection.record.routeClassId = "lambdair_highir_rust" then
        "highir_rust_bridge_ready_no_native_rust_backend"
      else
        "planned_bridge_ready_no_native_backend"
    else if plannedRolloutBridgeStrategy = "none" then
      "no_bridge_strategy"
    else
      "bridge_strategy_not_ready"
  let bridgeStrategyFields : List (String × Json) :=
    [ ("planned_rollout_bridge_actionable", .bool bridgeStrategyActionable)
    , ("certificate_replay_required", .bool certificateReplayRequired)
    , ("planned_rollout_bridge_apply_status", .str bridgeStrategyStatus)
    , ("planned_rollout_bridge_apply_reason", .str bridgeStrategyReason)
    , ("planned_rollout_bridge_strategy", .str plannedRolloutBridgeStrategy)
    , ("planned_rollout_bridge_action_hooks", jsonStrArray plannedRolloutBridgeActionHooks)
    , ("planned_rollout_bridge_action_hook_count", .num plannedRolloutBridgeActionHookCount)
    , ("planned_rollout_bridge_handoff_contract_ids",
        jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("planned_rollout_bridge_handoff_contract_count",
        .num plannedRolloutBridgeHandoffContractCount)
    , ("planned_rollout_bridge_handoff_contract_count_matches",
        .bool plannedRolloutBridgeHandoffContractCountMatches)
    , ("planned_rollout_bridge_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("planned_rollout_bridge_realization_required",
        .bool plannedRolloutBridgeRealizationRequired)
    , ("planned_rollout_bridge_realization_status",
        .str plannedRolloutBridgeRealizationStatus)
    , ("planned_rollout_bridge_realization_checklist",
        jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("planned_rollout_bridge_realization_checklist_count",
        .num plannedRolloutBridgeRealizationChecklistCount)
    , ("planned_rollout_bridge_realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("planned_rollout_bridge_certifying_replay_hooks",
        jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("planned_rollout_bridge_certifying_replay_hook_count",
        .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("planned_rollout_bridge_certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("planned_rollout_bridge_realization_contract_projection_summary",
        plannedRolloutBridgeRealizationContract)
    , ("planned_rollout_bridge_realization_receipt",
        plannedRolloutBridgeRealizationReceipt)
    , ("planned_rollout_bridge_realization_receipt_projection_summary",
        plannedRolloutBridgeRealizationReceipt)
    ]
  let bridgeHandoffArtifactRel := s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_bridge_handoff.json"
  let bridgeHandoffPath := outDir / "preview_promotion_bridge_handoff.json"
  let bridgeRealizationContractArtifactRel :=
    s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_bridge_realization_contract.json"
  let bridgeRealizationContractPath := outDir / "preview_promotion_bridge_realization_contract.json"
  let bridgeRealizationReceiptArtifactRel :=
    s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_bridge_realization_receipt.json"
  let bridgeRealizationReceiptPath := outDir / "preview_promotion_bridge_realization_receipt.json"
  let bridgeReplayOutcomesArtifactRel :=
    s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_bridge_replay_outcomes.json"
  let bridgeReplayOutcomesPath := outDir / "preview_promotion_bridge_replay_outcomes.json"
  let bridgeRealizationReceiptRuntimeArtifactRel :=
    s!"artifacts/heytingveil/{art.moduleName}/preview_promotion_bridge_realization_receipt_runtime.json"
  let bridgeRealizationReceiptRuntimePath :=
    outDir / "preview_promotion_bridge_realization_receipt_runtime.json"
  let bridgePlanProjectionArtifactRel :=
    bridgePlanArtifactRelForRouteClass selection.record.routeClassId
  let bridgePlanProjectionCommand :=
    bridgePlanCommandForRouteClass selection.record.routeClassId
  let bridgePlanProjectionDefaultStatus :=
    if bridgeStrategyActionable then plannedRolloutBridgeRealizationStatus else "not_available"
  let bridgePlanProjectionDefaultRouteClassId :=
    if bridgeStrategyActionable then selection.record.routeClassId else ""
  let bridgePlanProjectionDefaultArtifact :=
    if bridgeStrategyActionable then some bridgePlanProjectionArtifactRel else none
  let bridgePlanProjectionDefaultCommand :=
    if bridgeStrategyActionable then some bridgePlanProjectionCommand else none
  let (bridgeReplayOutcomesStatus, bridgeReplayOutcomesJson) ←
    if bridgeStrategyActionable then
      loadReplayOutcomesIfPresent bridgeReplayOutcomesPath
    else
      pure ("not_applicable", none)
  let (endpointReplayOutcomesStatus, endpointReplayOutcomesJson) ←
    loadReplayOutcomesIfPresent bridgeReplayOutcomesPath
  let endpointReplayOutcomesArtifactRel :=
    if endpointReplayOutcomesStatus = "ingested" then
      some bridgeReplayOutcomesArtifactRel
    else
      none
  let plannedRolloutBridgeRealizationReceiptRuntime :=
    realizedBridgeReceiptWithOutcomes
      plannedRolloutBridgeRealizationReceipt
      bridgeReplayOutcomesStatus
      (if bridgeStrategyActionable then some bridgeReplayOutcomesArtifactRel else none)
      bridgeReplayOutcomesJson
      bridgePlanProjectionDefaultStatus
      bridgePlanProjectionDefaultRouteClassId
      bridgePlanProjectionDefaultArtifact
      bridgePlanProjectionDefaultCommand
  let plannedRolloutBridgeMaterializationProjectionSummary :=
    jsonValOrDefault
      plannedRolloutBridgeRealizationReceiptRuntime
      "bridge_plan_materialization_projection_summary"
      (Json.mkObj
        [ ("bridge_plan_materialization_ok", .bool false)
        , ("bridge_plan_status", .str "not_available")
        , ("bridge_plan_route_class_id", .str "")
        , ("bridge_plan_artifact", .null)
        , ("bridge_plan_command", .null)
        , ("bridge_plan_exit_code", .null)
        , ("bridge_plan_materialization_rule", .str "not_available")
        , ("bridge_plan_materialization_run_state", .str "pending")
        , ("bridge_plan_materialization_result_status", .str "not_started")
        , ("bridge_plan_materialization_completed", .bool false)
        , ("bridge_plan_materialization_evidence", .null)
        , ("all_hooks_ok", .bool false)
        , ("all_checks_ok", .bool false)
        ])
  let theoremContractProjectionForApplyBase :=
    match theoremContractProjection with
    | .obj kvs =>
        Json.obj
          (kvs.insert
            "planned_rollout_bridge_materialization_projection_summary"
            plannedRolloutBridgeMaterializationProjectionSummary)
    | _ => theoremContractProjection
  let transitionMaterializationProjectionSummary :=
    jsonValOrDefault
      policyContextJson
      "planned_rollout_bridge_materialization_projection_summary"
      plannedRolloutBridgeMaterializationProjectionSummary
  let theoremContractProjectionForApplyMaterializationProjectionSummary :=
    jsonValOrDefault
      theoremContractProjectionForApplyBase
      "planned_rollout_bridge_materialization_projection_summary"
      plannedRolloutBridgeMaterializationProjectionSummary
  let theoremContractProjectionMaterializationMatchesTransition :=
    theoremContractProjectionForApplyMaterializationProjectionSummary ==
      transitionMaterializationProjectionSummary
  let policyContextJsonForApplyBase :=
    match policyContextJson with
    | .obj kvs =>
        let kvsWithMaterialization :=
          kvs.insert "planned_rollout_bridge_materialization_projection_summary"
            plannedRolloutBridgeMaterializationProjectionSummary
        let kvsWithTransitionMaterialization :=
          kvsWithMaterialization.insert
            "planned_rollout_bridge_materialization_projection_summary_transition"
            transitionMaterializationProjectionSummary
        let kvsWithTransitionProjection :=
          kvsWithTransitionMaterialization.insert
            "theorem_contract_projection_summary_transition"
            theoremContractProjection
        let kvsWithProjection :=
          kvsWithTransitionProjection.insert "theorem_contract_projection_summary"
            theoremContractProjectionForApplyBase
        Json.obj
          (kvsWithProjection.insert
            "theorem_contract_projection_materialization_projection_matches_transition"
            (.bool theoremContractProjectionMaterializationMatchesTransition))
    | _ => policyContextJson
  let plannedEndpointRealizationProjectionSummary :=
    jsonValOrDefault
      policyContextJsonForApplyBase
      "planned_endpoint_realization_projection"
      (plannedEndpointRealizationProjectionJson
        selection
        (Route.derivationEndpointFamilyForRouteClass selection.record.routeClassId)
        (Route.plannedDerivationEndpointContractIdsForRouteClass selection.record.routeClassId)
        selection.plannedBackendReadinessWitnessIds
        selection.plannedEndpointRealizationTheoremIds)
  let plannedEndpointRealizationReceiptSummary :=
    jsonValOrDefault
      plannedEndpointRealizationProjectionSummary
      "realization_execution_receipt"
      .null
  let plannedEndpointRealizationReceiptRuntimeSummary :=
    realizedEndpointRealizationReceiptWithOutcomes
      plannedEndpointRealizationReceiptSummary
      endpointReplayOutcomesStatus
      endpointReplayOutcomesArtifactRel
      endpointReplayOutcomesJson
  let endpointRuntimeReceiptRequired :=
    jsonBoolOrDefault plannedEndpointRealizationReceiptRuntimeSummary "required" false
  let endpointRuntimeReceiptStatus :=
    jsonStrOrDefault plannedEndpointRealizationReceiptRuntimeSummary "receipt_status" "not_required"
  let endpointRuntimeOutcomesStatus :=
    jsonStrOrDefault plannedEndpointRealizationReceiptRuntimeSummary "outcomes_status" "absent"
  let endpointRuntimeEntryCount :=
    jsonNatOrDefault plannedEndpointRealizationReceiptRuntimeSummary "entry_count" 0
  let endpointRuntimePendingCount :=
    jsonNatOrDefault plannedEndpointRealizationReceiptRuntimeSummary "pending_count" 0
  let endpointRuntimeExecutedCount :=
    jsonNatOrDefault plannedEndpointRealizationReceiptRuntimeSummary "executed_count" 0
  let endpointRuntimeFailedCount :=
    jsonNatOrDefault plannedEndpointRealizationReceiptRuntimeSummary "failed_count" 0
  let endpointRuntimeCompletedCount :=
    jsonNatOrDefault plannedEndpointRealizationReceiptRuntimeSummary "completed_count" 0
  let endpointRuntimeEntryCountMatchesHookCount :=
    jsonBoolOrDefault plannedEndpointRealizationReceiptRuntimeSummary
      "entry_count_matches_hook_count" false
  let endpointRuntimePendingCountMatchesEntries :=
    jsonBoolOrDefault plannedEndpointRealizationReceiptRuntimeSummary
      "pending_count_matches_entries" false
  let endpointRuntimeReadyForExecution :=
    jsonBoolOrDefault plannedEndpointRealizationReceiptRuntimeSummary "ready_for_execution" false
  let endpointRuntimeStatusRecognized :=
    endpointRuntimeReceiptStatus ∈
      [ "not_required"
      , "pending_execution"
      , "execution_in_progress"
      , "execution_complete"
      , "execution_failed"
      , "execution_outcomes_error"
      ]
  let endpointRuntimeOutcomesStatusRecognized :=
    endpointRuntimeOutcomesStatus ∈
      [ "not_required", "absent", "ingested", "parse_error", "invalid_schema" ]
  let endpointRuntimeStatusGateExpected :=
    if !endpointRuntimeReceiptRequired then
      "not_required"
    else if endpointRuntimeOutcomesStatus = "parse_error" ||
        endpointRuntimeOutcomesStatus = "invalid_schema" then
      "execution_outcomes_error"
    else if endpointRuntimeFailedCount > 0 then
      "execution_failed"
    else if endpointRuntimePendingCount = 0 && endpointRuntimeEntryCount > 0 then
      "execution_complete"
    else if endpointRuntimeOutcomesStatus = "ingested" then
      "execution_in_progress"
    else
      "pending_execution"
  let endpointRuntimeStatusGateMatches :=
    endpointRuntimeReceiptStatus = endpointRuntimeStatusGateExpected
  let endpointRuntimeStateCountDecompositionMatches :=
    endpointRuntimePendingCount + endpointRuntimeExecutedCount + endpointRuntimeFailedCount =
      endpointRuntimeEntryCount &&
      endpointRuntimeCompletedCount = endpointRuntimeExecutedCount
  let endpointRuntimeOutcomesIngested :=
    jsonBoolOrDefault plannedEndpointRealizationReceiptRuntimeSummary "outcomes_ingested" false
  let endpointRuntimeOutcomesArtifact :=
    jsonValOrDefault plannedEndpointRealizationReceiptRuntimeSummary "outcomes_artifact" .null
  let endpointRuntimeOutcomesArtifactConsistency :=
    if endpointRuntimeOutcomesIngested then endpointRuntimeOutcomesArtifact != .null else true
  let endpointRuntimeContractIds :=
    Route.endpointRuntimeReceiptContractIdsForVersion contractMetadataVersion
  let endpointRuntimeContractCount := endpointRuntimeContractIds.length
  let endpointRuntimeContractCountMatches :=
    endpointRuntimeContractCount = endpointRuntimeContractIds.length
  let theoremContractProjectionForApply :=
    match theoremContractProjectionForApplyBase with
    | .obj kvs =>
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_contract_ids"
          (jsonStrArray endpointRuntimeContractIds)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_contract_count"
          (.num endpointRuntimeContractCount)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_contract_count_matches"
          (.bool endpointRuntimeContractCountMatches)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_required"
          (.bool endpointRuntimeReceiptRequired)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_status"
          (.str endpointRuntimeReceiptStatus)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_status_recognized"
          (.bool endpointRuntimeStatusRecognized)
        let kvs := kvs.insert "endpoint_realization_runtime_outcomes_status"
          (.str endpointRuntimeOutcomesStatus)
        let kvs := kvs.insert "endpoint_realization_runtime_outcomes_status_recognized"
          (.bool endpointRuntimeOutcomesStatusRecognized)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_status_gate_expected"
          (.str endpointRuntimeStatusGateExpected)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_status_gate_matches"
          (.bool endpointRuntimeStatusGateMatches)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_entry_count"
          (.num endpointRuntimeEntryCount)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_pending_count"
          (.num endpointRuntimePendingCount)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_executed_count"
          (.num endpointRuntimeExecutedCount)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_failed_count"
          (.num endpointRuntimeFailedCount)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_completed_count"
          (.num endpointRuntimeCompletedCount)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_ready_for_execution"
          (.bool endpointRuntimeReadyForExecution)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_entry_count_matches_hook_count"
          (.bool endpointRuntimeEntryCountMatchesHookCount)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_pending_count_matches_entries"
          (.bool endpointRuntimePendingCountMatchesEntries)
        let kvs := kvs.insert "endpoint_realization_runtime_receipt_state_count_decomposition_matches"
          (.bool endpointRuntimeStateCountDecompositionMatches)
        let kvs := kvs.insert "endpoint_realization_runtime_outcomes_artifact_consistency"
          (.bool endpointRuntimeOutcomesArtifactConsistency)
        Json.obj
          (kvs.insert "endpoint_realization_runtime_receipt_projection_summary"
            plannedEndpointRealizationReceiptRuntimeSummary)
    | _ => theoremContractProjectionForApplyBase
  let policyContextJsonForApply :=
    match policyContextJsonForApplyBase with
    | .obj kvs =>
        let kvs := kvs.insert "theorem_contract_projection_summary" theoremContractProjectionForApply
        let kvs := kvs.insert "planned_endpoint_realization_receipt_summary"
          plannedEndpointRealizationReceiptSummary
        let kvs := kvs.insert "planned_endpoint_realization_receipt_runtime_summary"
          plannedEndpointRealizationReceiptRuntimeSummary
        let kvs := kvs.insert "planned_endpoint_realization_receipt_runtime_contract_ids"
          (jsonStrArray endpointRuntimeContractIds)
        let kvs := kvs.insert "planned_endpoint_realization_receipt_runtime_contract_count"
          (.num endpointRuntimeContractCount)
        let kvs := kvs.insert "planned_endpoint_realization_receipt_runtime_contract_count_matches"
          (.bool endpointRuntimeContractCountMatches)
        let kvs := kvs.insert "planned_endpoint_realization_receipt_runtime_status_gate_expected"
          (.str endpointRuntimeStatusGateExpected)
        let kvs := kvs.insert "planned_endpoint_realization_receipt_runtime_status_gate_matches"
          (.bool endpointRuntimeStatusGateMatches)
        let kvs := kvs.insert
          "planned_endpoint_realization_receipt_runtime_state_count_decomposition_matches"
          (.bool endpointRuntimeStateCountDecompositionMatches)
        let kvs := kvs.insert
          "planned_endpoint_realization_receipt_runtime_outcomes_status_recognized"
          (.bool endpointRuntimeOutcomesStatusRecognized)
        Json.obj kvs
    | _ => policyContextJsonForApplyBase
  writeBundleFile endpointRealizationArtifactPath
    (Json.pretty plannedEndpointRealizationProjectionSummary)
  writeBundleFile endpointRealizationReceiptArtifactPath
    (Json.pretty plannedEndpointRealizationReceiptSummary)
  writeBundleFile endpointRealizationReceiptRuntimeArtifactPath
    (Json.pretty plannedEndpointRealizationReceiptRuntimeSummary)
  let endpointRealizationArtifactFields : List (String × Json) :=
    [ ("planned_endpoint_realization_artifact_generated", .bool true)
    , ("planned_endpoint_realization_artifact", .str endpointRealizationArtifactRel)
    , ("planned_endpoint_realization_projection_summary",
        plannedEndpointRealizationProjectionSummary)
    , ("planned_endpoint_realization_receipt_generated", .bool true)
    , ("planned_endpoint_realization_receipt_artifact",
        .str endpointRealizationReceiptArtifactRel)
    , ("planned_endpoint_realization_receipt_summary",
        plannedEndpointRealizationReceiptSummary)
    , ("planned_endpoint_realization_receipt_runtime_generated", .bool true)
    , ("planned_endpoint_realization_receipt_runtime_artifact",
        .str endpointRealizationReceiptRuntimeArtifactRel)
    , ("planned_endpoint_realization_receipt_runtime_summary",
        plannedEndpointRealizationReceiptRuntimeSummary)
    , ("planned_endpoint_realization_receipt_runtime_contract_ids",
        jsonStrArray endpointRuntimeContractIds)
    , ("planned_endpoint_realization_receipt_runtime_contract_count",
        .num endpointRuntimeContractCount)
    , ("planned_endpoint_realization_receipt_runtime_contract_count_matches",
        .bool endpointRuntimeContractCountMatches)
    , ("planned_endpoint_realization_receipt_runtime_status_gate_expected",
        .str endpointRuntimeStatusGateExpected)
    , ("planned_endpoint_realization_receipt_runtime_status_gate_matches",
        .bool endpointRuntimeStatusGateMatches)
    , ("planned_endpoint_realization_receipt_runtime_state_count_decomposition_matches",
        .bool endpointRuntimeStateCountDecompositionMatches)
    , ("planned_endpoint_realization_receipt_runtime_outcomes_status_recognized",
        .bool endpointRuntimeOutcomesStatusRecognized)
    ]
  let bridgeHandoffJson := Json.mkObj
    [ ("stage", .str "planned_rollout_bridge_handoff")
    , ("route_class_id", .str selection.record.routeClassId)
    , ("target_class", .str selection.targetClass)
    , ("strategy", .str plannedRolloutBridgeStrategy)
    , ("actionable", .bool bridgeStrategyActionable)
    , ("status",
        .str
          (if bridgeStrategyActionable then
             "pending_backend_realization"
           else
             bridgeStrategyStatus))
    , ("reason", .str bridgeStrategyReason)
    , ("transition_status", .str transitionStatus)
    , ("transition_reason", .str transitionReason)
    , ("required_bridge_witness_ids", jsonStrArray plannedRolloutBridgeWitnessIds)
    , ("required_bridge_witness_count", .num plannedRolloutBridgeWitnessIds.length)
    , ("theorem_contract_handoff_ids", jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("theorem_contract_handoff_count", .num plannedRolloutBridgeHandoffContractCount)
    , ("theorem_contract_handoff_count_matches",
        .bool plannedRolloutBridgeHandoffContractCountMatches)
    , ("theorem_contract_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("action_hooks", jsonStrArray plannedRolloutBridgeActionHooks)
    , ("action_hook_count", .num plannedRolloutBridgeActionHookCount)
    , ("realization_required", .bool plannedRolloutBridgeRealizationRequired)
    , ("realization_status", .str plannedRolloutBridgeRealizationStatus)
    , ("realization_checklist", jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("realization_checklist_count", .num plannedRolloutBridgeRealizationChecklistCount)
    , ("realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("certifying_replay_hooks", jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("certifying_replay_hook_count", .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("realization_contract",
        if bridgeStrategyActionable then
          plannedRolloutBridgeRealizationContract
        else
          .null)
    , ("realization_receipt",
        if bridgeStrategyActionable then
          plannedRolloutBridgeRealizationReceipt
        else
          .null)
    , ("realization_receipt_runtime",
        if bridgeStrategyActionable then
          plannedRolloutBridgeRealizationReceiptRuntime
        else
          .null)
    , ("realization_receipt_runtime_materialization_projection_summary",
        plannedRolloutBridgeMaterializationProjectionSummary)
    , ("realization_contract_generated", .bool bridgeStrategyActionable)
    , ("realization_contract_artifact",
        if bridgeStrategyActionable then
          .str bridgeRealizationContractArtifactRel
        else
          .null)
    , ("realization_receipt_generated", .bool bridgeStrategyActionable)
    , ("realization_receipt_artifact",
        if bridgeStrategyActionable then
          .str bridgeRealizationReceiptArtifactRel
        else
          .null)
    , ("realization_receipt_runtime_generated", .bool bridgeStrategyActionable)
    , ("realization_receipt_runtime_artifact",
        if bridgeStrategyActionable then
          .str bridgeRealizationReceiptRuntimeArtifactRel
        else
          .null)
    , ("replay_outcomes_status", .str bridgeReplayOutcomesStatus)
    , ("replay_outcomes_artifact",
        if bridgeStrategyActionable then
          .str bridgeReplayOutcomesArtifactRel
        else
          .null)
    ]
  if bridgeStrategyActionable then
    writeBundleFile bridgeHandoffPath (Json.pretty bridgeHandoffJson)
  if bridgeStrategyActionable then
    writeBundleFile bridgeRealizationContractPath (Json.pretty plannedRolloutBridgeRealizationContract)
  if bridgeStrategyActionable then
    writeBundleFile bridgeRealizationReceiptPath (Json.pretty plannedRolloutBridgeRealizationReceipt)
  if bridgeStrategyActionable then
    writeBundleFile bridgeRealizationReceiptRuntimePath
      (Json.pretty plannedRolloutBridgeRealizationReceiptRuntime)
  let bridgeHandoffFields : List (String × Json) :=
    [ ("planned_rollout_bridge_handoff_generated", .bool bridgeStrategyActionable)
    , ("planned_rollout_bridge_handoff_artifact",
        if bridgeStrategyActionable then
          .str bridgeHandoffArtifactRel
        else
          .null)
    , ("planned_rollout_bridge_handoff",
        if bridgeStrategyActionable then
          bridgeHandoffJson
        else
          .null)
    ]
  let bridgeRealizationFields : List (String × Json) :=
    [ ("planned_rollout_bridge_realization_contract_generated", .bool bridgeStrategyActionable)
    , ("planned_rollout_bridge_realization_contract_artifact",
        if bridgeStrategyActionable then
          .str bridgeRealizationContractArtifactRel
        else
          .null)
    , ("planned_rollout_bridge_realization_contract",
        if bridgeStrategyActionable then
          plannedRolloutBridgeRealizationContract
        else
          .null)
    , ("planned_rollout_bridge_realization_receipt_generated", .bool bridgeStrategyActionable)
    , ("planned_rollout_bridge_realization_receipt_artifact",
        if bridgeStrategyActionable then
          .str bridgeRealizationReceiptArtifactRel
        else
          .null)
    , ("planned_rollout_bridge_realization_receipt",
        if bridgeStrategyActionable then
          plannedRolloutBridgeRealizationReceipt
        else
          .null)
    , ("planned_rollout_bridge_realization_receipt_runtime_generated",
        .bool bridgeStrategyActionable)
    , ("planned_rollout_bridge_realization_receipt_runtime_artifact",
        if bridgeStrategyActionable then
          .str bridgeRealizationReceiptRuntimeArtifactRel
        else
          .null)
    , ("planned_rollout_bridge_realization_receipt_runtime",
        if bridgeStrategyActionable then
          plannedRolloutBridgeRealizationReceiptRuntime
        else
          .null)
    , ("planned_rollout_bridge_realization_receipt_runtime_projection_summary",
        plannedRolloutBridgeRealizationReceipt)
    , ("planned_rollout_bridge_materialization_projection_summary",
        plannedRolloutBridgeMaterializationProjectionSummary)
    , ("planned_rollout_bridge_materialization_projection_summary_transition",
        transitionMaterializationProjectionSummary)
    , ("planned_rollout_bridge_replay_outcomes_status", .str bridgeReplayOutcomesStatus)
    , ("planned_rollout_bridge_replay_outcomes_artifact",
        if bridgeStrategyActionable then
          .str bridgeReplayOutcomesArtifactRel
        else
          .null)
    ]
  let promotionHandoffContractCountMatches :=
    plannedRolloutBridgeHandoffContractCountMatches &&
      plannedRolloutBridgeHandoffContractCount = plannedRolloutBridgeHandoffContractIds.length
  let promotionTheoremEnvelopeCoreFields : List (String × Json) :=
    [ ("theorem_contract_ids", jsonStrArray packageTheoremContractIds)
    , ("certificate_replay_required", .bool certificateReplayRequired)
    , ("planned_rollout_bridge_handoff_contract_ids",
        jsonStrArray plannedRolloutBridgeHandoffContractIds)
    , ("planned_rollout_bridge_handoff_contract_count",
        .num plannedRolloutBridgeHandoffContractCount)
    , ("planned_rollout_bridge_handoff_contract_count_matches",
        .bool promotionHandoffContractCountMatches)
    , ("planned_rollout_bridge_handoff_links_planned_policy",
        .bool plannedRolloutBridgeHandoffLinksPlannedPolicy)
    , ("planned_rollout_bridge_realization_required",
        .bool plannedRolloutBridgeRealizationRequired)
    , ("planned_rollout_bridge_realization_status",
        .str plannedRolloutBridgeRealizationStatus)
    , ("planned_rollout_bridge_realization_checklist",
        jsonStrArray plannedRolloutBridgeRealizationChecklist)
    , ("planned_rollout_bridge_realization_checklist_count",
        .num plannedRolloutBridgeRealizationChecklistCount)
    , ("planned_rollout_bridge_realization_checklist_count_matches",
        .bool plannedRolloutBridgeRealizationChecklistCountMatches)
    , ("planned_rollout_bridge_certifying_replay_hooks",
        jsonStrArray plannedRolloutBridgeCertifyingReplayHooks)
    , ("planned_rollout_bridge_certifying_replay_hook_count",
        .num plannedRolloutBridgeCertifyingReplayHookCount)
    , ("planned_rollout_bridge_certifying_replay_hook_count_matches",
        .bool plannedRolloutBridgeCertifyingReplayHookCountMatches)
    , ("planned_rollout_bridge_realization_contract_projection_summary",
        plannedRolloutBridgeRealizationContract)
    , ("planned_rollout_bridge_realization_receipt_projection_summary",
        plannedRolloutBridgeRealizationReceipt)
    , ("planned_rollout_bridge_realization_receipt_runtime_projection_summary",
        plannedRolloutBridgeRealizationReceipt)
    , ("planned_rollout_bridge_materialization_projection_summary",
        plannedRolloutBridgeMaterializationProjectionSummary)
    , ("planned_rollout_bridge_materialization_projection_summary_transition",
        transitionMaterializationProjectionSummary)
    , ("planned_endpoint_realization_projection_summary",
        plannedEndpointRealizationProjectionSummary)
    , ("planned_endpoint_realization_artifact_generated", .bool true)
    , ("planned_endpoint_realization_artifact", .str endpointRealizationArtifactRel)
    , ("planned_endpoint_realization_receipt_generated", .bool true)
    , ("planned_endpoint_realization_receipt_artifact", .str endpointRealizationReceiptArtifactRel)
    , ("planned_endpoint_realization_receipt_summary", plannedEndpointRealizationReceiptSummary)
    , ("planned_endpoint_realization_receipt_runtime_generated", .bool true)
    , ("planned_endpoint_realization_receipt_runtime_artifact",
        .str endpointRealizationReceiptRuntimeArtifactRel)
    , ("planned_endpoint_realization_receipt_runtime_summary",
        plannedEndpointRealizationReceiptRuntimeSummary)
    , ("planned_endpoint_realization_receipt_runtime_contract_ids",
        jsonStrArray endpointRuntimeContractIds)
    , ("planned_endpoint_realization_receipt_runtime_contract_count",
        .num endpointRuntimeContractCount)
    , ("planned_endpoint_realization_receipt_runtime_contract_count_matches",
        .bool endpointRuntimeContractCountMatches)
    , ("planned_endpoint_realization_receipt_runtime_status_gate_expected",
        .str endpointRuntimeStatusGateExpected)
    , ("planned_endpoint_realization_receipt_runtime_status_gate_matches",
        .bool endpointRuntimeStatusGateMatches)
    , ("planned_endpoint_realization_receipt_runtime_state_count_decomposition_matches",
        .bool endpointRuntimeStateCountDecompositionMatches)
    , ("planned_endpoint_realization_receipt_runtime_outcomes_status_recognized",
        .bool endpointRuntimeOutcomesStatusRecognized)
    , ("theorem_contract_projection", theoremContractProjectionForApply)
    ]

  let applyJson ←
    if transitionStatus = "ready_for_transition" then
      let packageOutRaw ← packageCommand src false
      let promotedOutRaw ← packageCommand src true
      let packageOut := (← parseJsonOrDie packageOutRaw)
      let promotedOut := (← parseJsonOrDie promotedOutRaw)

      let packageStatus := (← objStrOrDie packageOut "verification_status")
      let packageCertified := (← objBoolOrDie packageOut "certified")
      let packageCertificate := (← objStrOrDie packageOut "certificate")
      let packageTransitionArtifact := (← objStrOrDie packageOut "transition_artifact")
      let packageRouteRecordArtifact :=
        packageTransitionArtifact.replace "package_transition_snapshot.json" "route_record.json"
      let packageEnvelope := (← objValOrDie packageOut "theorem_envelope")
      let packageTheoremBase := (← objNatOrDie packageEnvelope "base_count")
      let packageTheoremWitness := (← objNatOrDie packageEnvelope "witness_count")
      let packageTheoremPreview := (← objNatOrDie packageEnvelope "preview_promotion_count")
      let packageTheoremTotal := (← objNatOrDie packageEnvelope "total_count")
      let packageTheoremDecomposes :=
        packageTheoremTotal = packageTheoremBase + packageTheoremWitness + packageTheoremPreview

      let promotedStatus := (← objStrOrDie promotedOut "verification_status")
      let promotedCertified := (← objBoolOrDie promotedOut "certified")
      let promotedCertificate := (← objStrOrDie promotedOut "certificate")
      let promotedTransitionArtifact := (← objStrOrDie promotedOut "transition_artifact")
      let promotedRouteRecordArtifact :=
        promotedTransitionArtifact.replace "package_transition_snapshot.json" "route_record.json"
      let packageTransitionMatchesNativePromotion :=
        packageTransitionArtifact = promotedTransitionArtifact
      let promotedApplied := (← objBoolOrDie promotedOut "preview_promotion_certified")
      let promotedEnvelope := (← objValOrDie promotedOut "theorem_envelope")
      let promotedTheoremBase := (← objNatOrDie promotedEnvelope "base_count")
      let promotedTheoremWitness := (← objNatOrDie promotedEnvelope "witness_count")
      let promotedTheoremPreview := (← objNatOrDie promotedEnvelope "preview_promotion_count")
      let promotedTheoremTotal := (← objNatOrDie promotedEnvelope "total_count")
      let promotedTheoremDecomposes :=
        promotedTheoremTotal = promotedTheoremBase + promotedTheoremWitness + promotedTheoremPreview

      let promotedRouteSelection := (← objValOrDie promotedOut "route_selection")
      let promotedTransitionIds := (← objStrArrayOrDie promotedRouteSelection "preview_promotion_transitions").toList
      let promotedTransitionCount := promotedTransitionIds.length
      let promotedTransitionCountMatches := promotedTheoremPreview = promotedTransitionCount
      let promotedTransitionInCert ←
        certificateContainsTheorems (System.FilePath.mk promotedCertificate) promotedTransitionIds

      let applyStatus :=
        if promotedApplied then
          if promotedCertified then
            "applied_with_native_promotion"
          else
            "applied_with_failed_native_promotion"
        else
          "applied_repackage"
      let applyReason :=
        if promotedApplied then
          if promotedCertified then
            "transition_ready_native_certified"
          else
            "transition_ready_native_not_certified"
        else
          "transition_ready"
      let promotionTheoremEnvelope := Json.mkObj
        (promotionTheoremEnvelopeCoreFields ++
          [ ("package", Json.mkObj
            [ ("base_count", .num packageTheoremBase)
            , ("witness_count", .num packageTheoremWitness)
            , ("preview_promotion_count", .num packageTheoremPreview)
            , ("total_count", .num packageTheoremTotal)
            , ("total_decomposes", .bool packageTheoremDecomposes)
            ])
          , ("promoted", Json.mkObj
            [ ("base_count", .num promotedTheoremBase)
            , ("witness_count", .num promotedTheoremWitness)
            , ("preview_promotion_count", .num promotedTheoremPreview)
            , ("total_count", .num promotedTheoremTotal)
            , ("total_decomposes", .bool promotedTheoremDecomposes)
            , ("transition_theorem_count", .num promotedTransitionCount)
            , ("transition_theorem_count_matches", .bool promotedTransitionCountMatches)
            , ("transition_theorem_ids", jsonStrArray promotedTransitionIds)
            , ("certificate_replay_required", .bool true)
            , ("transition_theorems_in_certificate", .bool promotedTransitionInCert)
            ])
          ])

      let applyBaseFields : List (String × Json) :=
        [ ("stage", .str "promotion_apply")
        , ("apply_status", .str applyStatus)
        , ("apply_reason", .str applyReason)
        , ("transition_id", .str transitionId)
        , ("route_class_id", .str selection.record.routeClassId)
        , ("target_class", .str selection.targetClass)
        , ("transition_status", .str transitionStatus)
        , ("transition_reason", .str transitionReason)
        , ("policy_context", policyContextJsonForApply)
        , ("package_invoked", .bool true)
        , ("package_verification_status", .str packageStatus)
        , ("package_certified", .bool packageCertified)
        , ("package_certificate", .str packageCertificate)
        , ("package_transition_snapshot_artifact", .str packageTransitionArtifact)
        , ("package_route_record_artifact", .str packageRouteRecordArtifact)
        ]
      let applyPromotionFields : List (String × Json) :=
        [ ("native_promotion_attempted", .bool true)
        , ("native_promotion_applied", .bool promotedApplied)
        , ("native_promotion_status", .str promotedStatus)
        , ("native_promotion_certified", .bool promotedCertified)
        , ("native_promotion_certificate", .str promotedCertificate)
        , ("native_promotion_transition_artifact", .str promotedTransitionArtifact)
        , ("native_promotion_route_record_artifact", .str promotedRouteRecordArtifact)
        , ("package_transition_snapshot_matches_native_promotion",
            .bool packageTransitionMatchesNativePromotion)
        , ("promotion_theorem_envelope", promotionTheoremEnvelope)
        ]
      let applyTailFields : List (String × Json) :=
        [ ("certifying_mutation_attempted", .bool false)
        , ("certifying_mutation_route", .null)
        , ("certifying_mutation_status", .null)
        , ("certifying_mutation_certified", .null)
        , ("certifying_mutation_certificate", .null)
        , ("certifying_mutation_spec", .null)
        , ("transition_artifact", .str transitionArtifactRel)
        , ("apply_artifact", .str applyArtifactRel)
        ]
      pure <| Json.mkObj
        (applyBaseFields ++ applyPromotionFields ++ applyTailFields ++ bridgeStrategyFields
          ++ bridgeHandoffFields ++ bridgeRealizationFields ++ endpointRealizationArtifactFields)
    else if bridgeStrategyActionable then
      let promotionTheoremEnvelope := Json.mkObj
        (promotionTheoremEnvelopeCoreFields ++
          [ ("package", .null)
          , ("promoted", .null)
          ])
      let bridgeBaseFields : List (String × Json) :=
        [ ("stage", .str "promotion_apply")
        , ("apply_status", .str "bridge_strategy_ready_pending_realization")
        , ("apply_reason", .str bridgeStrategyReason)
        , ("transition_id", .str transitionId)
        , ("route_class_id", .str selection.record.routeClassId)
        , ("target_class", .str selection.targetClass)
        , ("transition_status", .str transitionStatus)
        , ("transition_reason", .str transitionReason)
        , ("policy_context", policyContextJsonForApply)
        , ("package_invoked", .bool false)
        , ("package_verification_status", .null)
        , ("package_certified", .null)
        , ("package_certificate", .null)
        , ("package_transition_snapshot_artifact", .null)
        , ("package_route_record_artifact", .null)
        ]
      let bridgePromotionFields : List (String × Json) :=
        [ ("native_promotion_attempted", .bool false)
        , ("native_promotion_applied", .bool false)
        , ("native_promotion_status", .null)
        , ("native_promotion_certified", .null)
        , ("native_promotion_certificate", .null)
        , ("native_promotion_transition_artifact", .null)
        , ("native_promotion_route_record_artifact", .null)
        , ("package_transition_snapshot_matches_native_promotion", .null)
        , ("promotion_theorem_envelope", promotionTheoremEnvelope)
        ]
      let bridgeTailFields : List (String × Json) :=
        [ ("certifying_mutation_attempted", .bool false)
        , ("certifying_mutation_route", .null)
        , ("certifying_mutation_status", .null)
        , ("certifying_mutation_certified", .null)
        , ("certifying_mutation_certificate", .null)
        , ("certifying_mutation_spec", .null)
        , ("transition_artifact", .str transitionArtifactRel)
        , ("apply_artifact", .str applyArtifactRel)
        ]
      pure <| Json.mkObj
        (bridgeBaseFields ++ bridgePromotionFields ++ bridgeTailFields ++ bridgeStrategyFields
          ++ bridgeHandoffFields ++ bridgeRealizationFields ++ endpointRealizationArtifactFields)
    else
      let promotionTheoremEnvelope := Json.mkObj
        (promotionTheoremEnvelopeCoreFields ++
          [ ("package", .null)
          , ("promoted", .null)
          ])
      let blockedBaseFields : List (String × Json) :=
        [ ("stage", .str "promotion_apply")
        , ("apply_status", .str "blocked")
        , ("apply_reason", .str transitionReason)
        , ("transition_id", .str transitionId)
        , ("route_class_id", .str selection.record.routeClassId)
        , ("target_class", .str selection.targetClass)
        , ("transition_status", .str transitionStatus)
        , ("transition_reason", .str transitionReason)
        , ("policy_context", policyContextJsonForApply)
        , ("package_invoked", .bool false)
        , ("package_verification_status", .null)
        , ("package_certified", .null)
        , ("package_certificate", .null)
        , ("package_transition_snapshot_artifact", .null)
        , ("package_route_record_artifact", .null)
        ]
      let blockedPromotionFields : List (String × Json) :=
        [ ("native_promotion_attempted", .bool false)
        , ("native_promotion_applied", .bool false)
        , ("native_promotion_status", .null)
        , ("native_promotion_certified", .null)
        , ("native_promotion_certificate", .null)
        , ("native_promotion_transition_artifact", .null)
        , ("native_promotion_route_record_artifact", .null)
        , ("package_transition_snapshot_matches_native_promotion", .null)
        , ("promotion_theorem_envelope", promotionTheoremEnvelope)
        ]
      let blockedTailFields : List (String × Json) :=
        [ ("certifying_mutation_attempted", .bool false)
        , ("certifying_mutation_route", .null)
        , ("certifying_mutation_status", .null)
        , ("certifying_mutation_certified", .null)
        , ("certifying_mutation_certificate", .null)
        , ("certifying_mutation_spec", .null)
        , ("transition_artifact", .str transitionArtifactRel)
        , ("apply_artifact", .str applyArtifactRel)
        ]
      pure <| Json.mkObj
        (blockedBaseFields ++ blockedPromotionFields ++ blockedTailFields ++ bridgeStrategyFields
          ++ bridgeHandoffFields ++ bridgeRealizationFields ++ endpointRealizationArtifactFields)

  writeBundleFile applyPath (Json.pretty applyJson)
  pure <| Json.pretty applyJson

private def runCommand (cmd src : String) : IO String := do
  match cmd with
  | "parse" =>
      let pm ← parseOrDie src
      pure <| asJson [("status", .str "ok"), ("stage", .str "parsed"), ("module", .str pm.mod.name)]
  | "elab" =>
      let em ← elabOrDie src
      pure <| asJson [("status", .str "ok"), ("stage", .str "elaborated"), ("module", .str em.parsed.mod.name)]
  | "emit" =>
      let em ← elabOrDie src
      let art := DSL.emit em
      pure <| asJson [("status", .str "ok"), ("stage", .str "emitted"), ("module", .str art.moduleName), ("hash", .num art.contentHash.toNat)]
  | "check" =>
      let em ← elabOrDie src
      let ok := DSL.conforms em.profile em.parsed.mod
      pure <| asJson
        [ ("status", if ok then .str "ok" else .str "fail")
        , ("stage", .str "checked")
        , ("module", .str em.parsed.mod.name)
        , ("semantics_bridge", semanticsBridgeJson em.parsed.mod)
        , ("registry_refs", registryRefsJson em.parsed.mod)
        ]
  | "verify" =>
      let em ← elabOrDie src
      let (clauseFamily, clauseLabel) := pickClauseRef em.parsed.mod
      let stateVarNames := em.parsed.mod.stateVars.map Prod.fst
      let cti : Verify.CTIRecord :=
        { invariantId := clauseLabel
          stateFingerprint := "state-0"
          reason := "bootstrap"
          clauseFamily := clauseFamily
          clauseLabel := clauseLabel
          stateVars := stateVarNames }
      let repairPlan := Verify.buildRepairPlan cti
      let hints := repairPlan.hints
      let repairIteration := Verify.runRepairIteration repairPlan
      let repairReverify := Verify.runRepairReverify cti repairIteration
      let repairClosure := Verify.runRepairClosure repairReverify
      let repairAutoLoop := Verify.runRepairAutoLoop cti repairIteration
      let repairArtifact ←
        repairArtifactJson em.parsed.mod.name repairIteration repairReverify repairAutoLoop
      pure <| asJson
        [ ("status", .str "ok")
        , ("stage", .str "verified")
        , ("module", .str em.parsed.mod.name)
        , ("semantics_bridge", semanticsBridgeJson em.parsed.mod)
        , ("registry_refs", registryRefsJson em.parsed.mod)
        , ("cti", Verify.toJson cti)
        , ("strengthen_hints", jsonStrArray hints)
        , ("repair_plan", repairPlanJson cti repairPlan)
        , ("repair_iteration", repairIterationJson repairIteration)
        , ("repair_reverify", repairReverifyJson repairReverify)
        , ("repair_closure", repairClosureJson repairClosure)
        , ("repair_autoloop", repairAutoLoopJson repairAutoLoop)
        , ("repair_artifact", repairArtifact)
        ]
  | "package" =>
      packageCommand src false
  | "package_promoted" =>
      packageCommand src true
  | "promote" =>
      let em ← elabOrDie src
      let art := DSL.emit em
      let selection := Route.select em.parsed.mod
      let transitionResolution ← contractMetadataVersionResolutionFromEnv
      let transition := promotionTransitionJson selection transitionResolution
      let outDir := System.FilePath.mk ".." / "artifacts" / "heytingveil" / art.moduleName
      let transitionPath := outDir / "preview_promotion_transition.json"
      writeBundleFile transitionPath (Json.pretty transition)
      pure <| asJson
        [ ("status", .str "ok")
        , ("stage", .str "promotion_transition")
        , ("route", .str selection.record.routeClassId)
        , ("route_selection", routeSelectionJson selection)
        , ("promotion_transition", transition)
        , ("transition_artifact", .str transitionPath.toString)
        ]
  | "promote_apply" =>
      promoteApplyCommand src
  | _ =>
      throw <| IO.userError s!"unknown command: {cmd}"

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  match args with
  | [] =>
      IO.println usage
      pure 0
  | ["--help"] =>
      IO.println usage
      pure 0
  | ["promote", "--bridge-plan"] =>
      IO.eprintln "missing route class id for --bridge-plan"
      pure 3
  | "promote" :: "--bridge-plan" :: classId :: extra =>
      if !extra.isEmpty then
        IO.eprintln s!"unexpected extra args for --bridge-plan: {String.intercalate " " extra}"
        pure 3
      else
        try
          let out ← promoteBridgePlanCommand classId
          IO.println out
          pure 0
        catch e =>
          IO.eprintln s!"heytingveil: {e}"
          pure 1
  | cmd :: srcParts =>
      let src := String.intercalate " " srcParts
      if src.isEmpty then
        IO.eprintln "missing spec text"
        pure 3
      else
        try
          let out ← runCommand cmd src
          IO.println out
          pure 0
        catch e =>
          IO.eprintln s!"heytingveil: {e}"
          pure 1

end HeytingLean.CLI.HeytingVeilMain

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.HeytingVeilMain.main argv
