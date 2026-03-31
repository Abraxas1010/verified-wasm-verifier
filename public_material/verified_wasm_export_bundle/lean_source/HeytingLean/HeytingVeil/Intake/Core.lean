/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Routing.Core

/-!
# HeytingVeil Intake Core

Typed intake objects for user-facing prompt/spec orchestration before
formalization into the HeytingVeil verification lanes.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake

open HeytingLean.HeytingVeil.Routing

inductive IntakePhase
  | draft
  | refining
  | formalized
  deriving DecidableEq, Repr

structure ClarificationQuestion where
  key : String
  prompt : String
  deriving Repr

structure ClarificationAnswer where
  key : String
  value : String
  deriving Repr

structure SpecIntent where
  title : String
  userPrompt : String
  desiredProperty : String
  provenanceRef : Option String
  deriving Repr

inductive CheckpointStatus
  | pending
  | passed
  | failed
  deriving DecidableEq, Repr

structure RefinementCheckpoint where
  name : String
  status : CheckpointStatus
  note : String
  deriving DecidableEq, Repr

structure IntakeState where
  intent : SpecIntent
  phase : IntakePhase
  openQuestions : List ClarificationQuestion
  answers : List ClarificationAnswer
  checkpoints : List RefinementCheckpoint
  deriving Repr

structure FormalizationTicket where
  intent : SpecIntent
  normalizedSpec : String
  irClass : IRClass
  preferredBackend? : Option BackendClass
  deriving Repr

/-- Seed intake from a raw intent and initial clarification prompts. -/
def start (intent : SpecIntent) (qs : List ClarificationQuestion := []) : IntakeState :=
  {
    intent := intent
    phase := .draft
    openQuestions := qs
    answers := []
    checkpoints := []
  }

/-- Append an answer and move phase toward refinement/formalization. -/
def addAnswer (st : IntakeState) (ans : ClarificationAnswer) : IntakeState :=
  let remainingQs := st.openQuestions.filter (fun q => q.key ≠ ans.key)
  let nextPhase :=
    if remainingQs.isEmpty then IntakePhase.formalized else IntakePhase.refining
  {
    intent := st.intent
    phase := nextPhase
    openQuestions := remainingQs
    answers := st.answers ++ [ans]
    checkpoints := st.checkpoints
  }

/-- Add or replace a checkpoint entry by checkpoint name. -/
def setCheckpoint (st : IntakeState) (cp : RefinementCheckpoint) : IntakeState :=
  let others := st.checkpoints.filter (fun c => c.name ≠ cp.name)
  {
    intent := st.intent
    phase := st.phase
    openQuestions := st.openQuestions
    answers := st.answers
    checkpoints := others ++ [cp]
  }

/-- Promotion gate: all questions closed and no non-passed checkpoints remain. -/
def readyForTicket (st : IntakeState) : Bool :=
  st.openQuestions.isEmpty &&
    st.checkpoints.all (fun cp => decide (cp.status = CheckpointStatus.passed))

/-- Promote a formalized intake state into a route-ready ticket. -/
def toTicket (st : IntakeState) (normalizedSpec : String) (irClass : IRClass)
    (preferredBackend? : Option BackendClass := none) : FormalizationTicket :=
  {
    intent := st.intent
    normalizedSpec := normalizedSpec
    irClass := irClass
    preferredBackend? := preferredBackend?
  }

/-- Option-valued promotion that enforces `readyForTicket`. -/
def toTicketIfReady (st : IntakeState) (normalizedSpec : String) (irClass : IRClass)
    (preferredBackend? : Option BackendClass := none) : Option FormalizationTicket :=
  if readyForTicket st then
    some (toTicket st normalizedSpec irClass preferredBackend?)
  else
    none

end Intake
end HeytingVeil
end HeytingLean
