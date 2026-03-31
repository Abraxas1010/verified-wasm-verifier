import Lean

/-!
# HeytingLean.BountyHunter.YulMini.Types

Phase 1 input de-risking: a **minimal, Yul-adjacent AST** intended to be fed from
JSON (e.g. produced by an external Yul normalizer / extractor), but small enough
to evolve quickly.

This is *not* full Yul. It is the smallest subset we need to cover EtherStore-like
reentrancy patterns:

- storage reads/writes (`sload`, `sstore`)
- external call boundary (`call`)
- structured control (`if`)
- explicit `return`/`revert` terminators
-/

namespace HeytingLean.BountyHunter.YulMini

abbrev Ident := String

inductive Builtin where
  | sload (slot : Nat)
  | sstore (slot : Nat)
  | call (target : String)
  deriving Repr, Inhabited

inductive Expr where
  | var (x : Ident)
  | nat (n : Nat)
  | builtin (b : Builtin) (args : Array Expr)
  deriving Repr, Inhabited

inductive Stmt where
  | let_ (x : Ident) (e : Expr)
  | expr (e : Expr)
  | if_ (cond : Expr) (then_ : Array Stmt) (else_ : Array Stmt)
  | return_
  | revert
  deriving Repr, Inhabited

structure Func where
  name : String
  body : Array Stmt
  deriving Repr, Inhabited

structure Program where
  version : String := "yulmini.v1"
  funcs : Array Func
  deriving Repr, Inhabited

end HeytingLean.BountyHunter.YulMini
