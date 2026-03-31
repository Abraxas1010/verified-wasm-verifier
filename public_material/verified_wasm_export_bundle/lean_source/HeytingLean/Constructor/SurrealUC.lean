import HeytingLean.Constructor.UC
import HeytingLean.Numbers.SurrealCore
import HeytingLean.Constructor.SurrealAdapter

/-!
# Surreal-specific bridge for the UC scaffold

This module provides a minimal bridge from the abstract universal constructor
scaffold (`Constructor.UC`) to the Surreal pre-game substrate. It does not
impose any dynamics beyond what `UC` already assumes; instead it offers
simple interpretation helpers that turn codes and configurations into
`PreGame` and `Carrier` values.
-/

namespace HeytingLean
namespace Constructor
namespace SurrealUC

open Numbers
open Numbers.SurrealCore
open SurrealAdapter

/-- Interpret a UC `Code` as a Surreal pre-game. Currently this uses the code's
numeric payload as the `birth` index and keeps left/right moves empty, serving
as a lightweight baseline. -/
def codeToGame : Code → PreGame
  | Code.mk n => { L := [], R := [], birth := n }

/-- Interpret a UC configuration as a carrier element in the Surreal substrate
by collecting the pre-games corresponding to every code on its tape. -/
def configCarrier (cfg : Config) : Carrier :=
  { g | ∃ c ∈ cfg.tape, codeToGame c = g }

/-- Interpret the initial configuration of a universal constructor as an
ambient carrier element in the Surreal substrate. -/
def ucCarrier (u : UC) : Carrier :=
  configCarrier u.init

end SurrealUC
end Constructor
end HeytingLean
