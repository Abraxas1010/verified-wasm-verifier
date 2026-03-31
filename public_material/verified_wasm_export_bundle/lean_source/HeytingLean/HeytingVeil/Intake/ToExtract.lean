/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.Core
import HeytingLean.HeytingVeil.Routing.Core

/-!
# Intake -> Route Bridge

Bridge from user-facing intake tickets to route selection used by extraction
and packaging layers.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake

open HeytingLean.HeytingVeil.Routing

/-- Select the backend route requested by a formalization ticket. -/
def selectRouteForTicket (ticket : FormalizationTicket) : Route :=
  Routing.selectRoute ticket.irClass ticket.preferredBackend?

@[simp] theorem selectRouteForTicket_ir (ticket : FormalizationTicket) :
    (selectRouteForTicket ticket).ir = ticket.irClass := by
  show (Routing.selectRoute ticket.irClass ticket.preferredBackend?).ir = ticket.irClass
  exact Routing.selectRoute_ir ticket.irClass ticket.preferredBackend?

@[simp] theorem selectRouteForTicket_backend_default (ticket : FormalizationTicket)
    (hnone : ticket.preferredBackend? = none) :
    (selectRouteForTicket ticket).backend = Routing.defaultBackend ticket.irClass := by
  simp [selectRouteForTicket, hnone]

end Intake
end HeytingVeil
end HeytingLean
