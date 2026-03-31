import HeytingLean.BountyHunter.Solc.YulCore.CompileToEvmMini
import HeytingLean.BountyHunter.EvmMini.Semantics

/-!
# HeytingLean.BountyHunter.Solc.YulCore.Correctness

First correctness theorem lane:

`YulCore` (restricted, observer-only semantics) → `EvmMini` (observer-only semantics).

This is the minimal nucleus we can already connect to concrete EVM runs via
observer traces and certificates.
-/

namespace HeytingLean.BountyHunter.Solc.YulCore

theorem compile_preserves_observer_ops (ss : Array Stmt) :
    (HeytingLean.BountyHunter.EvmMini.run (compileToEvmMini ss)).ops = (traceOfStmts ss).ops := by
  -- `EvmMini` semantics is “observer-only”: running yields the trace obtained by
  -- reconstructing events from the compiled opcode kinds.
  --
  -- We prove correctness on the *ops projection* (order-only). A later phase will
  -- strengthen this statement to include key/value details.
  simp [HeytingLean.BountyHunter.EvmMini.run, HeytingLean.BountyHunter.EvmMini.toTrace,
    HeytingLean.BountyHunter.EvmTrace.Trace.ops,
    compileToEvmMini, traceOfStmts, traceOfEffects, effectsOfStmts]

end HeytingLean.BountyHunter.Solc.YulCore
