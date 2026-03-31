import Init.Data.Array.Lemmas
import HeytingLean.BountyHunter.EvmTrace.Types

/-!
# HeytingLean.BountyHunter.EvmMini.Types

`EvmMini` is a deliberately tiny semantics target used for the first
semantics-preservation theorem lane:

- we only model the *observer events* relevant to CEI (reads/writes/calls),
- we do not model the full EVM stack/memory/keccak/ABI yet.

This is meant to grow incrementally (without breaking the existing
observer-only certificates).
-/

namespace HeytingLean.BountyHunter.EvmMini

/-- An EvmMini program is a sequence of observer-relevant opcode kinds. -/
abbrev Program := Array String

/-- Convert opcode kinds into observer events. -/
def eventsOfOps (ops : Array String) : Array HeytingLean.BountyHunter.EvmTrace.Event :=
  ops.map (fun op => { op := op })

@[simp] theorem eventsOfOps_ops (ops : Array String) :
    (eventsOfOps ops).map (fun e => e.op) = ops := by
  apply Array.ext
  · simp [eventsOfOps]
  · intro i hi₁ hi₂
    simp [eventsOfOps] at *

/-- Convert an `EvmMini` program into an observer trace (identity projection). -/
def toTrace (p : Program) : HeytingLean.BountyHunter.EvmTrace.Trace :=
  { events := eventsOfOps p }

end HeytingLean.BountyHunter.EvmMini
