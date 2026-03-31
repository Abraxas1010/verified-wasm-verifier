import HeytingLean.LoF.LeanKernel.VerifierObligation

namespace HeytingLean.LoF.LeanKernel

open Lean

instance : ToJson ReplayKind where
  toJson kind := Json.str kind.asString

instance : FromJson ReplayKind where
  fromJson?
    | .str "whnf_call" => .ok .whnfCall
    | .str "whnf_step" => .ok .whnfStep
    | .str "tag_check" => .ok .tagCheck
    | json => .error s!"expected replay kind, got {json.compress}"

instance : ToJson DependencyRef where
  toJson dep :=
    Json.mkObj
      [ ("id", Json.str dep.id)
      , ("edge_kind", Json.str dep.edgeKind)
      ]

instance : FromJson DependencyRef where
  fromJson? json := do
    pure {
      id := ← json.getObjValAs? String "id"
      edgeKind := ← json.getObjValAs? String "edge_kind"
    }

instance : ToJson VerifierObligation where
  toJson obligation :=
    Json.mkObj
      [ ("id", Json.str obligation.id)
      , ("decl_name", Json.str obligation.declName)
      , ("decl_kind", Json.str obligation.declKind)
      , ("trace_role", Json.str obligation.traceRole)
      , ("trace_grain", Json.str obligation.traceGrain)
      , ("verification_mode", Json.str obligation.verificationMode)
      , ("replay_kind", toJson obligation.replayKind)
      , ("join_group", Json.str obligation.joinGroup)
      , ("deps", toJson obligation.deps)
      , ("projected_beta_zeta_steps", toJson obligation.projectedBetaZetaSteps)
      , ("step_count", toJson obligation.stepCount)
      , ("delta_iota_steps", toJson obligation.deltaIotaSteps)
      , ("node_count", toJson obligation.nodeCount)
      , ("input_expr_repr", Json.str obligation.inputExprRepr)
      , ("output_expr_repr", Json.str obligation.outputExprRepr)
      , ("native_whnf_repr", Json.str obligation.nativeWhnfRepr)
      , ("expected_tag_term", Json.str obligation.expectedTagTerm)
      , ("machine_json", obligation.machineJson)
      , ("final_json", obligation.finalJson)
      ]

private def getObjValD [FromJson α] (json : Json) (field : String) (fallback : α) : Except String α := do
  match json.getObjVal? field with
  | .ok value => fromJson? value
  | .error _ => pure fallback

private def getObjJsonD (json : Json) (field : String) (fallback : Json := Json.null) : Json :=
  match json.getObjVal? field with
  | .ok value => value
  | .error _ => fallback

def decodeVerifierObligation (json : Json) : Except String VerifierObligation := do
  pure {
    id := ← json.getObjValAs? String "id"
    declName := ← json.getObjValAs? String "decl_name"
    declKind := ← json.getObjValAs? String "decl_kind"
    traceRole := ← json.getObjValAs? String "trace_role"
    traceGrain := ← getObjValD json "trace_grain" "whnf"
    verificationMode := ← getObjValD json "verification_mode" "whnf_call"
    replayKind := ← getObjValD json "replay_kind" ReplayKind.whnfCall
    joinGroup := ← json.getObjValAs? String "join_group"
    deps := ← getObjValD json "deps" (#[]
      : Array DependencyRef)
    projectedBetaZetaSteps := ← getObjValD json "projected_beta_zeta_steps" 0
    stepCount := ← getObjValD json "step_count" 0
    deltaIotaSteps := ← getObjValD json "delta_iota_steps" 0
    nodeCount := ← getObjValD json "node_count" 0
    inputExprRepr := ← getObjValD json "input_expr_repr" ""
    outputExprRepr := ← getObjValD json "output_expr_repr" ""
    nativeWhnfRepr := ← getObjValD json "native_whnf_repr" ""
    expectedTagTerm := ← getObjValD json "expected_tag_term" ""
    machineJson := getObjJsonD json "machine_json"
    finalJson := getObjJsonD json "final_json"
  }

instance : FromJson VerifierObligation where
  fromJson? := decodeVerifierObligation

private def replayKindCountsToJson (counts : Array (String × Nat)) : Json :=
  Json.mkObj <| counts.toList.map fun (label, count) => (label, toJson count)

instance : ToJson VerifierArtifact where
  toJson artifact :=
    Json.mkObj
      [ ("schema_version", toJson artifact.schemaVersion)
      , ("format", Json.str artifact.formatName)
      , ("tool", Json.str artifact.toolName)
      , ("artifact_kind", Json.str artifact.artifactKind)
      , ("module", Json.str artifact.moduleName)
      , ("trace_grain", Json.str artifact.traceGrain)
      , ("join_strategy", Json.str artifact.joinStrategy)
      , ("selected_declarations", toJson artifact.selectedDeclarations)
      , ("total_declarations", toJson artifact.totalDeclarations)
      , ("trace_max_steps", toJson artifact.traceMaxSteps)
      , ("fuel_whnf", toJson artifact.fuelWhnf)
      , ("fuel_defeq", toJson artifact.fuelDefEq)
      , ("fuel_reduce", toJson artifact.fuelReduce)
      , ("max_nodes", toJson artifact.maxNodes)
      , ("eligible_trace_entries", toJson artifact.eligibleTraceEntries)
      , ("obligations_total", toJson artifact.obligationsTotal)
      , ("omitted_trace_entries", toJson artifact.omittedTraceEntries)
      , ("replay_kind_counts", replayKindCountsToJson artifact.replayKindCounts)
      , ("obligations", toJson artifact.obligations)
      , ("honest_assessment", Json.str artifact.honestAssessment)
      ]

def decodeVerifierArtifact (json : Json) : Except String VerifierArtifact := do
  pure {
    schemaVersion := ← getObjValD json "schema_version" 1
    formatName := ← getObjValD json "format" "sky-v1"
    toolName := ← getObjValD json "tool" "verified_check"
    artifactKind := ← getObjValD json "artifact_kind" "portable_verifier_obligations"
    moduleName := ← json.getObjValAs? String "module"
    traceGrain := ← getObjValD json "trace_grain" "whnf"
    joinStrategy := ← getObjValD json "join_strategy" "declaration_all_clean"
    selectedDeclarations := ← getObjValD json "selected_declarations" 0
    totalDeclarations := ← getObjValD json "total_declarations" 0
    traceMaxSteps := ← getObjValD json "trace_max_steps" 0
    fuelWhnf := ← getObjValD json "fuel_whnf" 0
    fuelDefEq := ← getObjValD json "fuel_defeq" 0
    fuelReduce := ← getObjValD json "fuel_reduce" 0
    maxNodes := ← getObjValD json "max_nodes" 0
    eligibleTraceEntries := ← getObjValD json "eligible_trace_entries" 0
    obligations := ← getObjValD json "obligations" (#[]
      : Array VerifierObligation)
    honestAssessment := ← getObjValD json "honest_assessment" ""
  }

def parseVerifierArtifact (json : Json) : Except String VerifierArtifact :=
  decodeVerifierArtifact json

instance : FromJson VerifierArtifact where
  fromJson? := parseVerifierArtifact

end HeytingLean.LoF.LeanKernel
