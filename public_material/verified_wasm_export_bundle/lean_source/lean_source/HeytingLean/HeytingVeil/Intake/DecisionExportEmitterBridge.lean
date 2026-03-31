/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.DecisionExport
import HeytingLean.HeytingVeil.Packaging.Emitter.Core

/-!
# Intake DecisionExport -> Packaging Emitter Bridge

Unifies target planning between intake decision export jobs and packaging
envelope emitter jobs.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake
namespace DecisionExportEmitterBridge

open HeytingLean.HeytingVeil.Intake.DecisionExport
open HeytingLean.HeytingVeil.Packaging.Emitter

/-- Target-map from intake decision export lane to packaging emitter lane. -/
def toEmitterTarget : DecisionExportTarget → EmissionTarget
  | .stdout => .stdout
  | .file path => .filePath path

structure UnifiedTargetPlan where
  decisionTarget : DecisionExportTarget
  emitterTarget : EmissionTarget
  decisionPlan : String
  emitterTargetLabel : String
  deriving Repr

private def emitterTargetLabelOf : EmissionTarget → String
  | .stdout => "stdout"
  | .filePath path => "file:" ++ path

/-- Build a unified orchestration plan from a decision export job. -/
def buildUnifiedTargetPlan (job : DecisionExportJob) : UnifiedTargetPlan :=
  let emitterTarget := toEmitterTarget job.target
  {
    decisionTarget := job.target
    emitterTarget := emitterTarget
    decisionPlan := DecisionExport.renderJobPlan job
    emitterTargetLabel := emitterTargetLabelOf emitterTarget
  }

/-- Render human-readable coordination plan for both lanes. -/
def renderUnifiedPlan (plan : UnifiedTargetPlan) : String :=
  String.intercalate "\n"
    [plan.decisionPlan, "emitter_target=" ++ plan.emitterTargetLabel]

theorem buildUnifiedTargetPlan_target_consistent (job : DecisionExportJob) :
    (buildUnifiedTargetPlan job).emitterTarget = toEmitterTarget job.target := by
  rfl

end DecisionExportEmitterBridge
end Intake
end HeytingVeil
end HeytingLean
