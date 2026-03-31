/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.DecisionExportEmitterBridge

/-!
# Intake DecisionExport -> Emitter Adapter

Compatibility adapter from intake decision-export jobs to packaging emitter
plan stubs (`spec/route/target`) and optional concrete emission jobs.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake
namespace DecisionExportEmitterAdapter

open HeytingLean.HeytingVeil.Intake.DecisionExport
open HeytingLean.HeytingVeil.Intake.DecisionExportEmitterBridge
open HeytingLean.HeytingVeil.Packaging.Emitter

structure EmitterCompatTuple where
  specIdHint : String
  route : String
  target : EmissionTarget
  envelopeReady : Bool
  bridgeExtractHook : String
  bridgeProofHook : String
  bridgeCabHook : String
  bridgeHooksReady : Bool
  integrityDigest : String
  deriving Repr

/-- Deterministic compatibility tuple from decision-export records. -/
def compatTuple (job : DecisionExportJob) : EmitterCompatTuple :=
  {
    specIdHint := job.record.decision.title
    route := job.record.resolvedRoute
    target := toEmitterTarget job.target
    envelopeReady := job.record.envelope?.isSome
    bridgeExtractHook := job.record.bridgeExtractHook
    bridgeProofHook := job.record.bridgeProofHook
    bridgeCabHook := job.record.bridgeCabHook
    bridgeHooksReady := job.record.bridgeHooksReady
    integrityDigest := job.record.integrityDigest
  }

/-- Promote to a concrete emitter job only when an envelope payload exists. -/
def toEmissionJob? (job : DecisionExportJob) : Option EmissionJob :=
  match job.record.envelope? with
  | some payload =>
      let t := compatTuple job
      some
        {
          specId := t.specIdHint
          route := t.route
          payload := payload
          target := t.target
        }
  | none => none

theorem compatTuple_target_consistent (job : DecisionExportJob) :
    (compatTuple job).target = toEmitterTarget job.target := by
  rfl

theorem compatTuple_route_consistent (job : DecisionExportJob) :
    (compatTuple job).route = job.record.resolvedRoute := by
  rfl

theorem compatTuple_specIdHint_consistent (job : DecisionExportJob) :
    (compatTuple job).specIdHint = job.record.decision.title := by
  rfl

theorem compatTuple_envelopeReady_consistent (job : DecisionExportJob) :
    (compatTuple job).envelopeReady = job.record.envelope?.isSome := by
  rfl

theorem compatTuple_integrityDigest_consistent (job : DecisionExportJob) :
    (compatTuple job).integrityDigest = job.record.integrityDigest := by
  rfl

theorem compatTuple_bridgeExtractHook_consistent (job : DecisionExportJob) :
    (compatTuple job).bridgeExtractHook = job.record.bridgeExtractHook := by
  rfl

theorem compatTuple_bridgeProofHook_consistent (job : DecisionExportJob) :
    (compatTuple job).bridgeProofHook = job.record.bridgeProofHook := by
  rfl

theorem compatTuple_bridgeCabHook_consistent (job : DecisionExportJob) :
    (compatTuple job).bridgeCabHook = job.record.bridgeCabHook := by
  rfl

theorem compatTuple_bridgeHooksReady_consistent (job : DecisionExportJob) :
    (compatTuple job).bridgeHooksReady = job.record.bridgeHooksReady := by
  rfl

theorem toEmissionJob?_none (job : DecisionExportJob) :
    job.record.envelope? = none -> toEmissionJob? job = none := by
  intro h
  simp [toEmissionJob?, h]

theorem toEmissionJob?_some (job : DecisionExportJob) (payload : String) :
    job.record.envelope? = some payload ->
      toEmissionJob? job =
        some
          {
            specId := (compatTuple job).specIdHint
            route := (compatTuple job).route
            payload := payload
            target := (compatTuple job).target
          } := by
  intro h
  simp [toEmissionJob?, h]

theorem toEmissionJob?_isSome_eq_envelope (job : DecisionExportJob) :
    (toEmissionJob? job).isSome = job.record.envelope?.isSome := by
  cases h : job.record.envelope? <;> simp [toEmissionJob?, h]

private def renderTupleTarget (target : EmissionTarget) : String :=
  match target with
  | .stdout => "stdout"
  | .filePath path => "file:" ++ path

/-- Human-readable adapter plan showing tuple plus concrete emission readiness. -/
def renderAdapterPlan (job : DecisionExportJob) : String :=
  let t := compatTuple job
  let tupleLines :=
    [
      "adapter_spec_id=" ++ t.specIdHint,
      "adapter_route=" ++ t.route,
      "adapter_target=" ++ renderTupleTarget t.target,
      "adapter_envelope_ready=" ++ toString t.envelopeReady,
      "adapter_bridge_extract_hook=" ++ t.bridgeExtractHook,
      "adapter_bridge_proof_hook=" ++ t.bridgeProofHook,
      "adapter_bridge_cab_hook=" ++ t.bridgeCabHook,
      "adapter_bridge_hooks_ready=" ++ toString t.bridgeHooksReady,
      "adapter_integrity_digest=" ++ t.integrityDigest
    ]
  let emitterLine :=
    match toEmissionJob? job with
    | some ej => "emitter_plan=" ++ renderPlan ej
    | none => "emitter_plan=blocked:no_envelope"
  String.intercalate "\n" (tupleLines ++ [emitterLine])

end DecisionExportEmitterAdapter
end Intake
end HeytingVeil
end HeytingLean
