/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.Core

/-!
# Intake Refinement Policy

Minimal deterministic policy hook that updates quality checkpoints before
ticket promotion.
S17+ extend the baseline gate with explicit blocker taxonomy and scoring so
demo diagnostics can explain *why* a ticket is blocked.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake
namespace Policy

/-! Policy blocker taxonomy (machine-readable diagnostics). -/
inductive PolicyBlocker
  | missingPrompt
  | missingProperty
  | openQuestions
  | missingProvenance
  deriving DecidableEq, Repr

private def checkpointPromptNonempty (st : IntakeState) : RefinementCheckpoint :=
  {
    name := "prompt_nonempty"
    status := if st.intent.userPrompt.isEmpty then CheckpointStatus.failed else CheckpointStatus.passed
    note := "User prompt must be non-empty"
  }

private def checkpointPropertyNonempty (st : IntakeState) : RefinementCheckpoint :=
  {
    name := "property_nonempty"
    status := if st.intent.desiredProperty.isEmpty then CheckpointStatus.failed else CheckpointStatus.passed
    note := "Desired property must be non-empty"
  }

private def checkpointQuestionsClosed (st : IntakeState) : RefinementCheckpoint :=
  {
    name := "questions_closed"
    status := if st.openQuestions.isEmpty then CheckpointStatus.passed else CheckpointStatus.pending
    note := "Open clarification questions should be closed"
  }

private def checkpointProvenancePresent (st : IntakeState) : RefinementCheckpoint :=
  {
    name := "provenance_present"
    status := if st.intent.provenanceRef.isSome then CheckpointStatus.passed else CheckpointStatus.failed
    note := "Provenance reference should be provided"
  }

/-- Deterministic baseline policy checkpoints. -/
def baselineCheckpoints (st : IntakeState) : List RefinementCheckpoint :=
  [checkpointPromptNonempty st, checkpointPropertyNonempty st,
   checkpointQuestionsClosed st, checkpointProvenancePresent st]

/-- Apply baseline policy by replacing checkpoints with policy output. -/
def applyBaselinePolicy (st : IntakeState) : IntakeState :=
  {
    intent := st.intent
    phase := st.phase
    openQuestions := st.openQuestions
    answers := st.answers
    checkpoints := baselineCheckpoints st
  }

structure PromotionDiagnostics where
  openQuestionKeys : List String
  passedCheckpoints : List String
  pendingCheckpoints : List String
  failedCheckpoints : List String
  deriving Repr

private def checkpointNamesWithStatus (st : IntakeState) (status : CheckpointStatus) : List String :=
  (st.checkpoints.filter (fun cp => cp.status = status)).map (fun cp => cp.name)

/-- Operator-facing readiness diagnostics for ticket promotion. -/
def promotionDiagnostics (st : IntakeState) : PromotionDiagnostics :=
  {
    openQuestionKeys := st.openQuestions.map (fun q => q.key)
    passedCheckpoints := checkpointNamesWithStatus st CheckpointStatus.passed
    pendingCheckpoints := checkpointNamesWithStatus st CheckpointStatus.pending
    failedCheckpoints := checkpointNamesWithStatus st CheckpointStatus.failed
  }

/-- Boolean decision surface matching `readyForTicket`. -/
def promotionPasses (diag : PromotionDiagnostics) : Bool :=
  diag.openQuestionKeys.isEmpty &&
    diag.pendingCheckpoints.isEmpty &&
    diag.failedCheckpoints.isEmpty

private def renderStringList (xs : List String) : String :=
  if xs.isEmpty then "-" else String.intercalate ", " xs

/-- Human-readable pass/fail summary for operator review. -/
def renderPromotionDiagnostics (diag : PromotionDiagnostics) : String :=
  let outcome := if promotionPasses diag then "PASS" else "BLOCKED"
  String.intercalate "\n"
    [
      s!"promotion_status={outcome}",
      s!"open_questions={renderStringList diag.openQuestionKeys}",
      s!"passed_checkpoints={renderStringList diag.passedCheckpoints}",
      s!"pending_checkpoints={renderStringList diag.pendingCheckpoints}",
      s!"failed_checkpoints={renderStringList diag.failedCheckpoints}"
    ]

/-- Apply baseline policy and return immediate promotion diagnostics. -/
def applyBaselinePolicyWithDiagnostics (st : IntakeState) : IntakeState × PromotionDiagnostics :=
  let st' := applyBaselinePolicy st
  (st', promotionDiagnostics st')

theorem applyBaselinePolicy_has_four_checkpoints (st : IntakeState) :
    (applyBaselinePolicy st).checkpoints.length = 4 := by
  simp [applyBaselinePolicy, baselineCheckpoints]

/-- Baseline policy guarantees readiness exactly when the user prompt and desired
property are non-empty, all clarification questions are answered, and provenance
metadata is present. -/
theorem applyBaselinePolicy_ready_of_closed_questions_and_nonempty_payload
    (st : IntakeState) (hPrompt : ¬ st.intent.userPrompt.isEmpty)
    (hProperty : ¬ st.intent.desiredProperty.isEmpty)
    (hQuestions : st.openQuestions.isEmpty)
    (hProvenance : st.intent.provenanceRef.isSome) :
    readyForTicket (applyBaselinePolicy st) = true := by
  simp [readyForTicket, applyBaselinePolicy, baselineCheckpoints,
    checkpointPromptNonempty, checkpointPropertyNonempty,
    checkpointQuestionsClosed, checkpointProvenancePresent,
    hPrompt, hProperty, hQuestions, hProvenance]

/-- If questions remain open, baseline policy cannot make the ticket ready. -/
theorem applyBaselinePolicy_not_ready_with_open_questions (st : IntakeState)
    (hQuestions : st.openQuestions.isEmpty = false) :
    readyForTicket (applyBaselinePolicy st) = false := by
  simp [readyForTicket, applyBaselinePolicy, hQuestions]

/-- Human-readable blocker tags in fixed order. -/
def blockerTag : PolicyBlocker → String
  | PolicyBlocker.missingPrompt => "missing_prompt"
  | PolicyBlocker.missingProperty => "missing_property"
  | PolicyBlocker.openQuestions => "questions_open"
  | PolicyBlocker.missingProvenance => "missing_provenance"

def baselineBlockers (st : IntakeState) : List PolicyBlocker :=
  (if st.intent.userPrompt.isEmpty then [PolicyBlocker.missingPrompt] else []) ++
    (if st.intent.desiredProperty.isEmpty then [PolicyBlocker.missingProperty] else []) ++
    (if st.openQuestions.isEmpty then [] else [PolicyBlocker.openQuestions]) ++
    (if st.intent.provenanceRef.isSome then [] else [PolicyBlocker.missingProvenance])

def joinWithComma (ss : List String) : String :=
  match ss with
  | [] => ""
  | [s] => s
  | s :: ss => s ++ ", " ++ joinWithComma ss

def baselinePolicyScore (st : IntakeState) : Nat :=
  4 - (baselineBlockers st |>.length)

def baselinePolicyMaxScore : Nat := 4

def baselinePolicyReady (st : IntakeState) : Bool :=
  decide (baselineBlockers st = [])

def baselinePolicyBlockerString (st : IntakeState) : String :=
  if baselinePolicyReady st then
    "ready_for_ticket"
  else
    "intake_checks_not_ready: " ++
      joinWithComma (baselineBlockers st |>.map blockerTag)

theorem baselinePolicyBlockerString_pass (st : IntakeState) :
    baselinePolicyReady st = true →
    baselinePolicyBlockerString st = "ready_for_ticket" := by
  intro h
  cases h' : baselinePolicyReady st with
  | false =>
      have : False := by
        simp [h'] at h
      cases this
  | true =>
      simp [baselinePolicyBlockerString, h']

theorem baselinePolicyScore_bounded (st : IntakeState) :
    baselinePolicyScore st ≤ baselinePolicyMaxScore := by
  simp [baselinePolicyScore, baselinePolicyMaxScore]

end Policy
end Intake
end HeytingVeil
end HeytingLean
