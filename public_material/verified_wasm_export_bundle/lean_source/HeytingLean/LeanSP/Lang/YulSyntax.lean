import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulObjectMini.Types

/-!
# LeanSP.Lang.YulSyntax

Re-exports existing YulTextMini and YulObjectMini types for the LeanSP namespace,
and adds new structures needed for value-level verification (FuncDef, YulUnit).

Constraint H6: We IMPORT these types — we do NOT redefine Lit/Expr/Stmt.
-/

namespace LeanSP.Yul

-- Re-export existing types for LeanSP namespace convenience (H6)
abbrev Lit := HeytingLean.BountyHunter.Solc.YulTextMini.Lit
abbrev Expr := HeytingLean.BountyHunter.Solc.YulTextMini.Expr
abbrev Stmt := HeytingLean.BountyHunter.Solc.YulTextMini.Stmt
abbrev Program := HeytingLean.BountyHunter.Solc.YulTextMini.Program
abbrev YulObjectItem := HeytingLean.BountyHunter.Solc.YulObjectMini.Item
abbrev YulObjectProgram := HeytingLean.BountyHunter.Solc.YulObjectMini.Program

/-- Structured function definition for semantics.
    YulTextMini stores functions as `(String × Array Stmt)` pairs — it drops
    parameter and return variable names because effect semantics doesn't need them.
    LeanSP's value-level semantics requires those names. -/
structure FuncDef where
  name : String
  params : Array String
  returns : Array String
  body : Array Stmt
  deriving Repr, Inhabited

/-- A Yul compilation unit: wraps parsed code body with extracted FuncDefs. -/
structure YulUnit where
  /-- Contract object name from solc output. -/
  objectName : String
  /-- Top-level statements in the code body (excluding function defs). -/
  topLevelStmts : Array Stmt
  /-- Functions extracted from the code body, with parameters resolved. -/
  functions : Array FuncDef
  deriving Repr, Inhabited

end LeanSP.Yul
