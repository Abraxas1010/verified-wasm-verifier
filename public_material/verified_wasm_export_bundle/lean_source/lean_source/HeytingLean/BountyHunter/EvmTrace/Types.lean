import Lean

namespace HeytingLean.BountyHunter.EvmTrace

/-- Optional details for an `SLOAD` observer event. -/
structure SLoad where
  key : String
  deriving Repr, Inhabited, DecidableEq

/-- Optional details for an `SSTORE` observer event. -/
structure SStore where
  key : String
  /-- Optional stored value (observer traces from a concrete EVM typically provide it; abstract traces may omit). -/
  value : Option String := none
  deriving Repr, Inhabited, DecidableEq

/-- Optional details for an external boundary event (`CALL` family). -/
structure Boundary where
  kind : String
  to : String
  /-- Optional value transferred. -/
  value : Option String := none
  /-- Optional gas forwarded (often dynamic; safe to omit in normalized comparisons). -/
  gas : Option String := none
  deriving Repr, Inhabited, DecidableEq

/-- A single observer-relevant EVM event (filtered). -/
structure Event where
  op : String
  sload : Option SLoad := none
  sstore : Option SStore := none
  boundary : Option Boundary := none
  deriving Repr, Inhabited, DecidableEq

/-- Minimal observer trace used for CEI and other phase-0 security checks. -/
structure Trace where
  version : String := "evm_observer_trace.v0"
  events : Array Event := #[]
  deriving Repr, Inhabited, DecidableEq

def Trace.ops (t : Trace) : Array String :=
  t.events.map (fun e => e.op)

end HeytingLean.BountyHunter.EvmTrace
