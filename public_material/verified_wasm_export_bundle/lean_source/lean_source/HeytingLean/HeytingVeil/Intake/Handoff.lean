/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.Policy

/-!
# Intake Operator Handoff

Records that carry policy diagnostics and ticket-promotion status for operator
review before extraction/routing/export steps.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake
namespace Handoff

open HeytingLean.HeytingVeil.Routing
open HeytingLean.HeytingVeil.Intake.Policy

structure OperatorHandoff where
  title : String
  irClass : IRClass
  preferredBackend? : Option BackendClass
  promotionPasses : Bool
  diagnostics : PromotionDiagnostics
  ticket? : Option FormalizationTicket
  deriving Repr

/-- Build a diagnostics-first handoff record from intake state. -/
def build (st : IntakeState) (normalizedSpec : String) (irClass : IRClass)
    (preferredBackend? : Option BackendClass := none) : OperatorHandoff :=
  let assessed := applyBaselinePolicyWithDiagnostics st
  let stPolicy := assessed.fst
  let diag := assessed.snd
  let ticket? := toTicketIfReady stPolicy normalizedSpec irClass preferredBackend?
  {
    title := st.intent.title
    irClass := irClass
    preferredBackend? := preferredBackend?
    promotionPasses := promotionPasses diag
    diagnostics := diag
    ticket? := ticket?
  }

/-- Human-readable diagnostics rendered from the handoff payload. -/
def renderDiagnostics (handoff : OperatorHandoff) : String :=
  renderPromotionDiagnostics handoff.diagnostics

/-- Render pass/block status plus diagnostics and optional emitted payload. -/
def renderWithPayload (handoff : OperatorHandoff) (payload : String) : String :=
  match handoff.ticket? with
  | some _ =>
      String.intercalate "\n"
        ["promotion_lane=PASS", s!"handoff_title={handoff.title}", renderDiagnostics handoff, "envelope=" ++ payload]
  | none =>
      String.intercalate "\n"
        ["promotion_lane=BLOCKED", s!"handoff_title={handoff.title}", renderDiagnostics handoff]

end Handoff
end Intake
end HeytingVeil
end HeytingLean
