import Lean
import Std

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.Types

Minimal Yul-text AST for parsing Solidity `ir` / `irOptimized` output.

This is intentionally tiny: it is only meant to support extraction of the
effects needed for Phase 1 checks (e.g. CEI).
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

inductive Lit where
  | nat (n : Nat)
  | str (s : String)
  | bool (b : Bool)
  deriving Repr, Inhabited

structure Func where
  name : String
  bodyTokens : Array String := #[]
  deriving Repr, DecidableEq, Inhabited

/-! We parse function bodies as a statement AST (for CFG construction). -/

inductive Expr where
  | ident (name : String)
  | nat (n : Nat)
  | str (s : String)
  | bool (b : Bool)
  | call (fn : String) (args : Array Expr)
  deriving Repr, Inhabited

inductive Stmt where
  | let_ (name : String) (rhs : Expr)
  /-- Multiple bindings (e.g. `let a, b := f(...)`). We do not model tuple semantics; this is for parsing/effect extraction. -/
  | letMany (names : Array String) (rhs : Expr)
  | assign (name : String) (rhs : Expr)
  /-- Multiple assignment (e.g. `a, b := f(...)`). We do not model tuple semantics; this is for parsing/effect extraction and codegen stability. -/
  | assignMany (names : Array String) (rhs : Expr)
  | expr (e : Expr)
  | if_ (cond : Expr) (thenStmts : Array Stmt)
  | switch_ (scrut : Expr) (cases : Array (Lit × Array Stmt)) (default? : Option (Array Stmt))
  | for_ (init : Array Stmt) (cond : Expr) (post : Array Stmt) (body : Array Stmt)
  | break
  | continue
  | block (stmts : Array Stmt)
  | return_ (args : Array Expr)
  | revert (args : Array Expr)
  | leave
  deriving Repr, Inhabited

structure Program where
  version : String := "yultextmini.v0"
  funcs : Array (String × Array Stmt) := #[]
  deriving Repr, Inhabited

end HeytingLean.BountyHunter.Solc.YulTextMini
