import HeytingLean.KernelAssurance.ObligationManifest

namespace HeytingLean.Tests.KernelAssurance

open Lean
open HeytingLean.KernelAssurance
open HeytingLean.LoF.LeanKernel

private def dep (id edgeKind : String) : DependencyRef :=
  { id := id, edgeKind := edgeKind }

private def whnfObligation : VerifierObligation :=
  { id := "Fixture.thm:type:whnf"
    declName := "Fixture.thm"
    declKind := "theorem"
    traceRole := "type"
    traceGrain := "whnf"
    verificationMode := "whnf_call"
    replayKind := .whnfCall
    joinGroup := "Fixture.thm"
    projectedBetaZetaSteps := 2
    stepCount := 2
    deltaIotaSteps := 0
    nodeCount := 8
    inputExprRepr := "Nat.succ 0"
    outputExprRepr := "1"
    nativeWhnfRepr := "1"
    machineJson := Json.mkObj [("tag", Json.str "machine"), ("value", Json.str "ok")]
    finalJson := Json.mkObj [("tag", Json.str "final"), ("value", Json.str "1")] }

private def inferObligation : VerifierObligation :=
  { id := "Fixture.thm:infer_type_sort"
    declName := "Fixture.thm"
    declKind := "theorem"
    traceRole := "declaration_operation"
    traceGrain := "machine_export"
    verificationMode := "infer_type_sort"
    replayKind := .tagCheck
    joinGroup := "Fixture.thm"
    deps := #[dep "Fixture.thm:type:whnf" "operation_dep"]
    stepCount := 1
    nodeCount := 5
    inputExprRepr := "Nat"
    outputExprRepr := "Sort"
    expectedTagTerm := "sort"
    machineJson := Json.mkObj [("tag", Json.str "machine"), ("value", Json.str "infer")]
    finalJson := Json.mkObj [("tag", Json.str "final"), ("value", Json.str "Sort")] }

private def checkObligation : VerifierObligation :=
  { id := "Fixture.thm:check_value"
    declName := "Fixture.thm"
    declKind := "theorem"
    traceRole := "declaration_operation"
    traceGrain := "machine_export"
    verificationMode := "check_value"
    replayKind := .tagCheck
    joinGroup := "Fixture.thm"
    deps := #[dep "Fixture.thm:infer_type_sort" "operation_dep"]
    stepCount := 1
    nodeCount := 4
    inputExprRepr := "0"
    outputExprRepr := "true"
    expectedTagTerm := "true"
    machineJson := Json.mkObj [("tag", Json.str "machine"), ("value", Json.str "check")]
    finalJson := Json.mkObj [("tag", Json.str "final"), ("value", Json.str "true")] }

private def blockedWhnfStep : VerifierObligation :=
  { id := "Fixture.thm:value:step"
    declName := "Fixture.thm"
    declKind := "theorem"
    traceRole := "value"
    traceGrain := "whnf"
    verificationMode := "whnf_call"
    replayKind := .whnfStep
    joinGroup := "Fixture.thm"
    stepCount := 1
    nodeCount := 3
    inputExprRepr := "id 0"
    outputExprRepr := "0"
    nativeWhnfRepr := "0"
    machineJson := Json.mkObj [("tag", Json.str "machine"), ("value", Json.str "step")]
    finalJson := Json.mkObj [("tag", Json.str "final"), ("value", Json.str "0")] }

private def unknownMode : VerifierObligation :=
  { id := "Fixture.thm:mystery"
    declName := "Fixture.thm"
    declKind := "theorem"
    traceRole := "declaration_operation"
    traceGrain := "machine_export"
    verificationMode := "mystery_mode"
    replayKind := .tagCheck
    joinGroup := "Fixture.thm"
    stepCount := 1
    nodeCount := 2
    inputExprRepr := "?"
    outputExprRepr := "?"
    machineJson := Json.mkObj [("tag", Json.str "machine"), ("value", Json.str "mystery")]
    finalJson := Json.mkObj [("tag", Json.str "final"), ("value", Json.str "mystery")] }

def supportedArtifact : VerifierArtifact :=
  { moduleName := "HeytingLean.Tests.KernelAssurance.Fixture"
    traceGrain := "mixed"
    selectedDeclarations := 1
    totalDeclarations := 1
    traceMaxSteps := 64
    fuelWhnf := 20
    fuelDefEq := 20
    fuelReduce := 100
    maxNodes := 128
    eligibleTraceEntries := 3
    obligations := #[whnfObligation, inferObligation, checkObligation]
    honestAssessment := "Fixture obligation artifact for kernel assurance tests." }

def mixedArtifact : VerifierArtifact :=
  { supportedArtifact with
    eligibleTraceEntries := 5
    obligations := #[whnfObligation, inferObligation, blockedWhnfStep, unknownMode] }

def supportedObligationBundle : ObligationSliceBundle :=
  ObligationSliceBundle.ofArtifact supportedArtifact

def mixedObligationBundle : ObligationSliceBundle :=
  ObligationSliceBundle.ofArtifact mixedArtifact

def tamperedObligationBundle : ObligationSliceBundle :=
  let entry0 := supportedObligationBundle.entries[0]!
  let tampered0 : ObligationEntry := { entry0 with machineDigest := "tampered" }
  let tamperedEntries := supportedObligationBundle.entries.set! 0 tampered0
  { supportedObligationBundle with entries := tamperedEntries }

private def sourceScopeWhnfObligation : VerifierObligation :=
  { id := "Scoped.Fixture:whnf_type"
    declName := "Scoped.Fixture"
    declKind := "theorem"
    traceRole := "declaration_operation"
    traceGrain := "machine_export"
    verificationMode := "whnf_type"
    replayKind := .tagCheck
    joinGroup := "Scoped.Fixture"
    stepCount := 1
    nodeCount := 4
    inputExprRepr := "Nat"
    outputExprRepr := "Sort"
    expectedTagTerm := "sort"
    machineJson := Json.mkObj [("tag", Json.str "machine"), ("value", Json.str "whnf")]
    finalJson := Json.mkObj [("tag", Json.str "final"), ("value", Json.str "Sort")] }

def sourceScopeArtifact : VerifierArtifact :=
  { moduleName := "HeytingLean.Tests.KernelAssurance.SourceScope"
    traceGrain := "machine_export"
    selectedDeclarations := 1
    totalDeclarations := 1
    traceMaxSteps := 64
    fuelWhnf := 20
    fuelDefEq := 20
    fuelReduce := 100
    maxNodes := 128
    eligibleTraceEntries := 1
    obligations := #[sourceScopeWhnfObligation]
    honestAssessment := "Fixture artifact with a narrower exported slice than the discovered source payload." }

def sourceScopeBundle : ObligationSliceBundle :=
  ObligationSliceBundle.ofArtifact sourceScopeArtifact

def sourceScopePayload : Json :=
  Json.mkObj
    [ ("module", Json.str "HeytingLean.Tests.KernelAssurance.SourceScope")
    , ("selected_declarations", toJson (1 : Nat))
    , ("total_declarations", toJson (1 : Nat))
    , ("declarations",
        Json.arr #[
          Json.mkObj
            [ ("decl_name", Json.str "Scoped.Fixture")
            , ("decl_kind", Json.str "theorem")
            , ("operations",
                Json.arr #[
                  Json.mkObj
                    [ ("op_type", Json.str "whnf_type")
                    , ("eligible", Json.bool true)
                    , ("semantic_check_skipped", Json.bool false)
                    ],
                  Json.mkObj
                    [ ("op_type", Json.str "infer_value")
                    , ("eligible", Json.bool false)
                    , ("semantic_check_skipped", Json.bool false)
                    ]
                ])
            ]
        ])
    ]

def sourceScopeICCExport : Json :=
  Json.mkObj
    [ ("moduleRoots", Json.arr #[Json.str "HeytingLean.Tests.KernelAssurance.SourceScope"])
    , ("summary",
        Json.mkObj
          [ ("declsTotal", toJson (2 : Nat))
          , ("declsSupported", toJson (2 : Nat))
          , ("declsUnsupported", toJson (0 : Nat))
          , ("declsUnclassified", toJson (0 : Nat))
          ])
    ]

def sourceScopeICCNoLoss : Json :=
  Json.mkObj
    [ ("ok", Json.bool true)
    , ("moduleRoots", Json.arr #[Json.str "HeytingLean.Tests.KernelAssurance.SourceScope"])
    , ("modulesChecked", toJson (1 : Nat))
    , ("declsSeen", toJson (2 : Nat))
    , ("declsChecked", toJson (2 : Nat))
    , ("failuresCount", toJson (0 : Nat))
    , ("failures", Json.arr #[])
    ]

def sourceScopeICCNoLossMismatch : Json :=
  Json.mkObj
    [ ("ok", Json.bool false)
    , ("moduleRoots", Json.arr #[Json.str "HeytingLean.Tests.KernelAssurance.SourceScope"])
    , ("modulesChecked", toJson (1 : Nat))
    , ("declsSeen", toJson (2 : Nat))
    , ("declsChecked", toJson (1 : Nat))
    , ("failuresCount", toJson (1 : Nat))
    , ("failures", Json.arr #[Json.mkObj [("stage", Json.str "bundle-recover")]])
    ]

end HeytingLean.Tests.KernelAssurance
