import HeytingLean.BountyHunter.Solc.YulCore.ObsTrace
import HeytingLean.BountyHunter.EvmMini.Types

/-!
# HeytingLean.BountyHunter.Solc.YulCore.CompileToEvmMini

Phase-1 “compiler” from `YulCore` into `EvmMini`.

Today this is defined via the observer semantics spine:
we compile a statement list to the sequence of observer opcode kinds produced by
the `YulCore` observer trace.

Later phases will replace this with a genuine bytecode compiler (u256/stack/ABI),
and this module becomes the stable interface point for correctness theorems.
-/

namespace HeytingLean.BountyHunter.Solc.YulCore

def compileToEvmMini (ss : Array Stmt) : HeytingLean.BountyHunter.EvmMini.Program :=
  -- Note: `EvmMini.Program` is `Array String`, and our trace stores the op kind.
  (traceOfStmts ss).events.map (fun e => e.op)

end HeytingLean.BountyHunter.Solc.YulCore
