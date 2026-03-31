/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import Lean.Data.Json

/-!
# HeytingVeil Error Taxonomy

Structured error codes with actionable recovery hints for CLI and agent workflows.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Errors

inductive Severity where
  | error
  | warning
  | info
  deriving Repr, Inhabited, BEq

def Severity.tag : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .info => "info"

structure ErrorInfo where
  errorCode : String
  message : String
  recoveryHint : String
  severity : Severity
  deriving Repr, Inhabited

inductive HeytingVeilError where
  | intakeBlocked (details : String)
  | routeFailure (details : String)
  | emissionFailure (details : String)
  | contractFailure (details : String)
  | runtimeFailure (details : String)
  | verifyFailure (details : String)
  | parseFailure (details : String)
  | ioFailure (details : String)
  | unsupported (details : String)
  deriving Repr, Inhabited

def toInfo : HeytingVeilError → ErrorInfo
  | .intakeBlocked details =>
      { errorCode := "HV-INTAKE-001"
      , message := details
      , recoveryHint := "Revise payload fields per blocker diagnostics and retry intake."
      , severity := .error }
  | .routeFailure details =>
      { errorCode := "HV-ROUTE-001"
      , message := details
      , recoveryHint := "Adjust target backends or extraction basis to a supported route."
      , severity := .error }
  | .emissionFailure details =>
      { errorCode := "HV-EMIT-001"
      , message := details
      , recoveryHint := "Check extraction adapter compatibility and backend payload constraints."
      , severity := .error }
  | .contractFailure details =>
      { errorCode := "HV-CONTRACT-001"
      , message := details
      , recoveryHint := "Treat as a pipeline contract regression; inspect envelope structure and cert fields."
      , severity := .error }
  | .runtimeFailure details =>
      { errorCode := "HV-RUNTIME-001"
      , message := details
      , recoveryHint := "Inspect generated source payload and runtime command assumptions."
      , severity := .error }
  | .verifyFailure details =>
      { errorCode := "HV-VERIFY-001"
      , message := details
      , recoveryHint := "Adjust property, bound, or refinement budget and rerun verification."
      , severity := .error }
  | .parseFailure details =>
      { errorCode := "HV-PARSE-001"
      , message := details
      , recoveryHint := "Fix malformed JSON/CLI arguments and retry."
      , severity := .error }
  | .ioFailure details =>
      { errorCode := "HV-IO-001"
      , message := details
      , recoveryHint := "Validate file paths, executable availability, and permissions."
      , severity := .error }
  | .unsupported details =>
      { errorCode := "HV-UNSUPPORTED-001"
      , message := details
      , recoveryHint := "Choose a supported command/backend/schema version."
      , severity := .warning }

def ErrorInfo.toJson (e : ErrorInfo) : Lean.Json :=
  Lean.Json.mkObj
    [ ("error_code", Lean.Json.str e.errorCode)
    , ("message", Lean.Json.str e.message)
    , ("recovery_hint", Lean.Json.str e.recoveryHint)
    , ("severity", Lean.Json.str e.severity.tag)
    ]

def HeytingVeilError.toJson (e : HeytingVeilError) : Lean.Json :=
  (toInfo e).toJson

def mkErrorObject (e : HeytingVeilError) : Lean.Json :=
  Lean.Json.mkObj [("status", Lean.Json.str "error"), ("error", e.toJson)]

end Errors
end HeytingVeil
end HeytingLean
