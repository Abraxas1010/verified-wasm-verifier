/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.Handoff

/-!
# Intake Decision Artifacts

Machine-readable, deterministic records for orchestration/management layers.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake
namespace Artifact

open HeytingLean.HeytingVeil.Routing
open HeytingLean.HeytingVeil.Intake.Handoff
open HeytingLean.HeytingVeil.Intake.Policy

structure DecisionArtifact where
  schemaVersion : String
  title : String
  requestedRoute : String
  promotionLane : String
  ticketPresent : Bool
  openQuestions : List String
  passedCheckpoints : List String
  pendingCheckpoints : List String
  failedCheckpoints : List String
  deriving Repr

private def laneOf (handoff : OperatorHandoff) : String :=
  if handoff.ticket?.isSome then "PASS" else "BLOCKED"

/-- Convert an operator handoff into a machine-readable decision artifact. -/
def fromHandoff (handoff : OperatorHandoff) : DecisionArtifact :=
  let diag := handoff.diagnostics
  {
    schemaVersion := "heytingveil.intake.decision.v1"
    title := handoff.title
    requestedRoute := Routing.routeLabel (Routing.selectRoute handoff.irClass handoff.preferredBackend?)
    promotionLane := laneOf handoff
    ticketPresent := handoff.ticket?.isSome
    openQuestions := diag.openQuestionKeys
    passedCheckpoints := diag.passedCheckpoints
    pendingCheckpoints := diag.pendingCheckpoints
    failedCheckpoints := diag.failedCheckpoints
  }

private def escapeJson (s : String) : String :=
  (((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n")

private def renderJsonStringList (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map (fun s => "\"" ++ escapeJson s ++ "\"")) ++ "]"

/-- Deterministic JSON-like artifact rendering for orchestration tooling. -/
def renderJson (a : DecisionArtifact) : String :=
  String.intercalate ""
    [
      "{",
      "\"schemaVersion\":\"", escapeJson a.schemaVersion, "\",",
      "\"title\":\"", escapeJson a.title, "\",",
      "\"requestedRoute\":\"", escapeJson a.requestedRoute, "\",",
      "\"promotionLane\":\"", escapeJson a.promotionLane, "\",",
      "\"ticketPresent\":", toString a.ticketPresent, ",",
      "\"openQuestions\":", renderJsonStringList a.openQuestions, ",",
      "\"passedCheckpoints\":", renderJsonStringList a.passedCheckpoints, ",",
      "\"pendingCheckpoints\":", renderJsonStringList a.pendingCheckpoints, ",",
      "\"failedCheckpoints\":", renderJsonStringList a.failedCheckpoints,
      "}"
    ]

end Artifact
end Intake
end HeytingVeil
end HeytingLean
