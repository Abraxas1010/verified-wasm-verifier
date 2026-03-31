import Std
import HeytingLean.BountyHunter.AlgebraIR.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse
import HeytingLean.BountyHunter.Solc.YulTextMini.Pretty

/-!
# HeytingLean.BountyHunter.AlgebraIR.BackYulTextMini

Sprint 3 “bidirectional subset” artifact:

`AlgebraIR` → a minimal YulTextMini *effects-only* program.

This is not a semantics-preserving decompiler. It is an **audit spine** that:
- deterministically renders the observed effects back into a parseable Yul subset,
- enables parse/pretty idempotence checks to catch accidental non-determinism.
-/

namespace HeytingLean.BountyHunter.AlgebraIR
namespace BackYulTextMini

open HeytingLean.BountyHunter.Solc.YulTextMini

private def parseSlotExprE (s : String) : Except String Expr :=
  parseExprFromStringE s

private def effectToStmtE : Effect → Except String Stmt
  | .storageRead slot =>
      pure (.expr (.call "sload" #[.nat slot]))
  | .storageReadDyn slotExpr => do
      let e ← parseSlotExprE slotExpr
      pure (.expr (.call "sload" #[e]))
  | .storageWrite slot =>
      pure (.expr (.call "sstore" #[.nat slot, .nat 0]))
  | .storageWriteDyn slotExpr => do
      let e ← parseSlotExprE slotExpr
      pure (.expr (.call "sstore" #[e, .nat 0]))
  | .boundaryCall target =>
      pure (.expr (.call target #[]))

def programFromGraphE (g : Graph) : Except String (Array Stmt) := do
  let mut out : Array Stmt := #[]
  for n in g.nodes do
    for eff in n.effects do
      out := out.push (← effectToStmtE eff)
  return out

def programFromPathE (g : Graph) (path : Array NodeId) : Except String (Array Stmt) := do
  let mut out : Array Stmt := #[]
  for id in path do
    match g.nodes.find? (fun n => n.id = id) with
    | none => pure ()
    | some n =>
        for eff in n.effects do
          out := out.push (← effectToStmtE eff)
  return out

def programToStringE (g : Graph) : Except String String := do
  let ss ← programFromGraphE g
  pure (stmtsToCanonicalString ss)

def programToStringFromPathE (g : Graph) (path : Array NodeId) : Except String String := do
  let ss ← programFromPathE g path
  pure (stmtsToCanonicalString ss)

end BackYulTextMini
end HeytingLean.BountyHunter.AlgebraIR
