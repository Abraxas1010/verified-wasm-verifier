/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.DecisionExportEmitterAdapter

/-!
# Intake Dispatch Intent

One-shot typed handoff payload combining decision export, target unification,
and emitter compatibility metadata.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake
namespace DispatchIntent

open HeytingLean.HeytingVeil.Intake.DecisionExport
open HeytingLean.HeytingVeil.Intake.DecisionExportEmitterBridge
open HeytingLean.HeytingVeil.Intake.DecisionExportEmitterAdapter
open HeytingLean.HeytingVeil.Packaging.Emitter

structure DispatchIntent where
  decisionJob : DecisionExportJob
  unifiedPlan : UnifiedTargetPlan
  adapterTuple : EmitterCompatTuple
  emissionJob? : Option EmissionJob
  dispatchReady : Bool
  deriving Repr

/-- Build a dispatch-intent payload from a decision export job. -/
def build (job : DecisionExportJob) : DispatchIntent :=
  let unifiedPlan := buildUnifiedTargetPlan job
  let adapterTuple := compatTuple job
  let emissionJob? := toEmissionJob? job
  {
    decisionJob := job
    unifiedPlan := unifiedPlan
    adapterTuple := adapterTuple
    emissionJob? := emissionJob?
    dispatchReady := emissionJob?.isSome
  }

theorem dispatchReady_eq_emission_isSome (job : DecisionExportJob) :
    (build job).dispatchReady = (build job).emissionJob?.isSome := by
  rfl

theorem build_dispatchReady_eq_envelope_isSome (job : DecisionExportJob) :
    (build job).dispatchReady = job.record.envelope?.isSome := by
  simp [build, toEmissionJob?_isSome_eq_envelope]

theorem build_unifiedDecisionTarget_eq_jobTarget (job : DecisionExportJob) :
    (build job).unifiedPlan.decisionTarget = job.target := by
  rfl

theorem build_unifiedEmitterTarget_eq_adapterTarget (job : DecisionExportJob) :
    (build job).unifiedPlan.emitterTarget = (build job).adapterTuple.target := by
  simp [build, buildUnifiedTargetPlan, compatTuple]

def decisionTargetLabel : DecisionExportTarget → String
  | .stdout => "stdout"
  | .file path => "file:" ++ path

def emitterTargetLabel : EmissionTarget → String
  | .stdout => "stdout"
  | .filePath path => "file:" ++ path

theorem build_target_labels_aligned (job : DecisionExportJob) :
    decisionTargetLabel (build job).unifiedPlan.decisionTarget =
      emitterTargetLabel (build job).adapterTuple.target := by
  calc
    decisionTargetLabel (build job).unifiedPlan.decisionTarget
        = decisionTargetLabel job.target := by
            simp [build_unifiedDecisionTarget_eq_jobTarget]
    _ = emitterTargetLabel (toEmitterTarget job.target) := by
          cases job.target <;> rfl
    _ = emitterTargetLabel (build job).adapterTuple.target := by
          simp [build, compatTuple_target_consistent]

private def escapeJson (s : String) : String :=
  (((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n")

private def emitterPlanString (intent : DispatchIntent) : String :=
  match intent.emissionJob? with
  | some ej => renderPlan ej
  | none => "blocked:no_envelope"

/-- Render a deterministic orchestration handoff summary. -/
def render (intent : DispatchIntent) : String :=
  let header :=
    [
      "dispatch_ready=" ++ toString intent.dispatchReady,
      "dispatch_route=" ++ intent.adapterTuple.route,
      "dispatch_spec_id=" ++ intent.adapterTuple.specIdHint,
      "dispatch_bridge_hooks_ready=" ++ toString intent.adapterTuple.bridgeHooksReady,
      "dispatch_bridge_extract_hook=" ++ intent.adapterTuple.bridgeExtractHook,
      "dispatch_bridge_proof_hook=" ++ intent.adapterTuple.bridgeProofHook,
      "dispatch_bridge_cab_hook=" ++ intent.adapterTuple.bridgeCabHook
    ]
  let plan := renderUnifiedPlan intent.unifiedPlan
  let emitterLine :=
    match intent.emissionJob? with
    | some ej => "dispatch_emitter_plan=" ++ renderPlan ej
    | none => "dispatch_emitter_plan=blocked:no_envelope"
  String.intercalate "\n" (header ++ [plan, emitterLine])

/-- Compact machine-ingestable JSON rendering for dispatch handoff payloads. -/
def renderJson (intent : DispatchIntent) : String :=
  String.intercalate ""
    [
      "{",
      "\"dispatchReady\":", toString intent.dispatchReady, ",",
      "\"dispatchRoute\":\"", escapeJson intent.adapterTuple.route, "\",",
      "\"dispatchSpecId\":\"", escapeJson intent.adapterTuple.specIdHint, "\",",
      "\"bridgeHooksReady\":", toString intent.adapterTuple.bridgeHooksReady, ",",
      "\"bridgeExtractHook\":\"", escapeJson intent.adapterTuple.bridgeExtractHook, "\",",
      "\"bridgeProofHook\":\"", escapeJson intent.adapterTuple.bridgeProofHook, "\",",
      "\"bridgeCabHook\":\"", escapeJson intent.adapterTuple.bridgeCabHook, "\",",
      "\"decisionTarget\":\"", escapeJson (decisionTargetLabel intent.decisionJob.target), "\",",
      "\"emitterTarget\":\"", escapeJson (emitterTargetLabel intent.adapterTuple.target), "\",",
      "\"emitterPlan\":\"", escapeJson (emitterPlanString intent), "\",",
      "\"decisionRecord\":", DecisionExport.renderRecordJson intent.decisionJob.record,
      "}"
    ]

end DispatchIntent
end Intake
end HeytingVeil
end HeytingLean
