/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.Artifact

/-!
# Intake Decision Export

Typed export lane for operator/orchestration systems that need both decision
artifacts and optional CAB-carrying envelope payloads.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake
namespace DecisionExport

open HeytingLean.HeytingVeil.Intake.Handoff
open HeytingLean.HeytingVeil.Intake.Artifact
open HeytingLean.HeytingVeil.Routing

inductive DecisionExportTarget
  | stdout
  | file (path : String)
  deriving Repr

structure DecisionExportRecord where
  decision : DecisionArtifact
  resolvedRoute : String
  envelope? : Option String
  cabAttached : Bool
  bridgeExtractHook : String
  bridgeProofHook : String
  bridgeCabHook : String
  bridgeHooksReady : Bool
  integrityDigest : String
  deriving Repr

structure DecisionExportJob where
  target : DecisionExportTarget
  record : DecisionExportRecord
  deriving Repr

/-- Build export record from a handoff and candidate envelope payload. -/
private def envelopeDigestTag (envelope? : Option String) : String :=
  match envelope? with
  | some payload => "some:" ++ toString payload.length
  | none => "none"

private def computeIntegrityDigest (decision : DecisionArtifact) (envelope? : Option String)
    (resolvedRoute : String)
    (bridgeExtractHook : String)
    (bridgeProofHook : String)
    (bridgeCabHook : String)
    (bridgeHooksReady : Bool) : String :=
  String.intercalate "|"
    [
      decision.schemaVersion,
      decision.title,
      resolvedRoute,
      decision.promotionLane,
      toString decision.ticketPresent,
      envelopeDigestTag envelope?,
      bridgeExtractHook,
      bridgeProofHook,
      bridgeCabHook,
      toString bridgeHooksReady
    ]

private def bridgeHooksForIRClass (ir : IRClass) :
    String × String × String × Bool :=
  match ir with
  | .lambdaNat =>
      ("Extract.Examples.NatFragmentAdapter.add1Bridge",
       "Extract.Examples.NatFragmentAdapter.add1_adapter_source_safety",
       "Packaging.Examples.NatBridgeCAB.add1_cab_compliant",
       true)
  | .lambdaNat2 =>
      ("Extract.Examples.Nat2FragmentAdapter.add2Bridge",
       "Extract.Examples.Nat2FragmentAdapter.add2_adapter_source_safety",
       "Packaging.Examples.NatBridgeCAB.add2_cab_compliant",
       true)
  | .miniCCore =>
      ("Extract.Core:miniCCore_unassigned",
       "Verify.Core:miniCCore_unassigned",
       "Packaging.Core:miniCCore_unassigned",
       false)
  | .generic =>
      ("Extract.Core:generic_unassigned",
       "Verify.Core:generic_unassigned",
       "Packaging.Core:generic_unassigned",
       false)

def recordFromHandoff (handoff : OperatorHandoff) (envelopePayload : String) : DecisionExportRecord :=
  let envelope? := if handoff.ticket?.isSome then some envelopePayload else none
  let resolvedRoute := Routing.routeLabel (Routing.selectRoute handoff.irClass handoff.preferredBackend?)
  let decision := Artifact.fromHandoff handoff
  let hooks := bridgeHooksForIRClass handoff.irClass
  {
    decision := decision
    resolvedRoute := resolvedRoute
    envelope? := envelope?
    cabAttached := envelope?.isSome
    bridgeExtractHook := hooks.1
    bridgeProofHook := hooks.2.1
    bridgeCabHook := hooks.2.2.1
    bridgeHooksReady := hooks.2.2.2
    integrityDigest :=
      computeIntegrityDigest decision envelope? resolvedRoute
        hooks.1 hooks.2.1 hooks.2.2.1 hooks.2.2.2
  }

/-- Build export job with a concrete output target. -/
def jobFromHandoff (handoff : OperatorHandoff) (envelopePayload : String)
    (target : DecisionExportTarget := .stdout) : DecisionExportJob :=
  {
    target := target
    record := recordFromHandoff handoff envelopePayload
  }

private def renderEnvelopeField (envelope? : Option String) : String :=
  let escapeJson := fun (s : String) =>
    (((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n")
  match envelope? with
  | some payload => "\"" ++ escapeJson payload ++ "\""
  | none => "null"

private def escapeJson (s : String) : String :=
  (((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n")

/-- Deterministic JSON-like rendering for downstream export jobs. -/
def renderRecordJson (record : DecisionExportRecord) : String :=
  String.intercalate ""
    [
      "{",
      "\"decision\":", Artifact.renderJson record.decision, ",",
      "\"resolvedRoute\":\"", escapeJson record.resolvedRoute, "\",",
      "\"cabAttached\":", toString record.cabAttached, ",",
      "\"bridgeExtractHook\":\"", escapeJson record.bridgeExtractHook, "\",",
      "\"bridgeProofHook\":\"", escapeJson record.bridgeProofHook, "\",",
      "\"bridgeCabHook\":\"", escapeJson record.bridgeCabHook, "\",",
      "\"bridgeHooksReady\":", toString record.bridgeHooksReady, ",",
      "\"envelope\":", renderEnvelopeField record.envelope?, ",",
      "\"integrityDigest\":\"", escapeJson record.integrityDigest, "\"",
      "}"
    ]

def renderBridgeHookSummary (record : DecisionExportRecord) : String :=
  String.intercalate "\n"
    [
      "bridge_extract_hook=" ++ record.bridgeExtractHook,
      "bridge_proof_hook=" ++ record.bridgeProofHook,
      "bridge_cab_hook=" ++ record.bridgeCabHook,
      "bridge_hooks_ready=" ++ toString record.bridgeHooksReady
    ]

/-- Render a stable execution plan for export orchestration. -/
def renderJobPlan (job : DecisionExportJob) : String :=
  let header :=
    match job.target with
    | .stdout => "export_target=stdout"
    | .file path => "export_target=file:" ++ path
  String.intercalate "\n"
    [header, "export_payload=" ++ renderRecordJson job.record]

end DecisionExport
end Intake
end HeytingVeil
end HeytingLean
