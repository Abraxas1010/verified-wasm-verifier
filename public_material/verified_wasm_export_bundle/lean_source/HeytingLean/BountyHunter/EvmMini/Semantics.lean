import HeytingLean.BountyHunter.EvmMini.Types

/-!
# HeytingLean.BountyHunter.EvmMini.Semantics

Phase-1 semantics for `EvmMini`: executing a program yields its observer trace.

This is intentionally “observer-only”. A later phase will introduce:
- u256 values, stack, memory, storage,
- a concrete semantics for `CALL` (at least for `value` transfers),
- and a connection to a real EVM semantics oracle.
-/

namespace HeytingLean.BountyHunter.EvmMini

def run (p : Program) : HeytingLean.BountyHunter.EvmTrace.Trace :=
  toTrace p

@[simp] theorem run_eq_toTrace (p : Program) : run p = toTrace p := by
  rfl

end HeytingLean.BountyHunter.EvmMini

