import Lean
import HeytingLean.Embedding.Ast

namespace HeytingLean.Embedding

open Lean

/-!
`lambda_core` extractor: a small, type-erased "lambda calculus core" view of elaborated `Expr`.

This is intentionally conservative and stable:
- binder types and universe annotations are erased (we keep bodies/values)
- `forallE` is treated like an untyped binder (encoded as `AstNode.lam`)
- the JSON schema stays identical to the existing `AstTree` schema (node.kind/value + children)

Canonicalization (bucketing of names, const tailing, etc.) is performed on the Python side so we
can iterate quickly without re-extracting the entire corpus.
-/

private def litToString : Literal → String
  | .natVal n => s!"nat:{n}"
  | .strVal s => s!"str:{s}"

/-- Convert a Lean `Expr` into a type-erased `lambda_core` AST (with bounded node count). -/
partial def exprToLambdaCoreAst (e : Expr) (maxNodes : Nat := 20000) : AstTree × Bool :=
  let rec go (fuel : Nat) (e : Expr) : (Option AstTree × Nat × Bool) :=
    if fuel = 0 then
      (none, 0, true)
    else
      match e with
      | .bvar idx =>
        (some { node := .bvar idx, children := #[] }, fuel - 1, false)
      | .fvar id =>
        (some { node := .fvar id.name.toString, children := #[] }, fuel - 1, false)
      | .const name _ =>
        (some { node := .const name.toString, children := #[] }, fuel - 1, false)
      | .lit l =>
        (some { node := .lit (litToString l), children := #[] }, fuel - 1, false)
      | .mdata _ inner =>
        go fuel inner
      | .mvar _ =>
        (some { node := .other "mvar", children := #[] }, fuel - 1, false)
      | .sort _ =>
        (some { node := .other "sort", children := #[] }, fuel - 1, false)
      | .app fn arg =>
        let (fnT?, fuel, t1) := go (fuel - 1) fn
        let (argT?, fuel, t2) := go fuel arg
        let children : Array AstTree :=
          match fnT? with
          | none => #[]
          | some t => #[t]
        let children : Array AstTree :=
          match argT? with
          | none => children
          | some t => children.push t
        let trunc := t1 || t2 || fnT?.isNone || argT?.isNone
        (some { node := .app, children }, fuel, trunc)
      | .lam binderName _type body _ =>
        let (bodyT?, fuel, t1) := go (fuel - 1) body
        let children : Array AstTree :=
          match bodyT? with
          | none => #[]
          | some t => #[t]
        let trunc := t1 || bodyT?.isNone
        (some { node := .lam binderName.toString, children }, fuel, trunc)
      | .forallE binderName _type body _ =>
        -- Treat Pi binders as untyped lambdas for the core view.
        let (bodyT?, fuel, t1) := go (fuel - 1) body
        let children : Array AstTree :=
          match bodyT? with
          | none => #[]
          | some t => #[t]
        let trunc := t1 || bodyT?.isNone
        (some { node := .lam binderName.toString, children }, fuel, trunc)
      | .letE binderName _type value body _ =>
        let (valT?, fuel, t1) := go (fuel - 1) value
        let (bodyT?, fuel, t2) := go fuel body
        let children : Array AstTree :=
          match valT? with
          | none => #[]
          | some t => #[t]
        let children : Array AstTree :=
          match bodyT? with
          | none => children
          | some t => children.push t
        let trunc := t1 || t2 || valT?.isNone || bodyT?.isNone
        (some { node := .letE binderName.toString, children }, fuel, trunc)
      | .proj structName idx structExpr =>
        let (innerT?, fuel, t1) := go (fuel - 1) structExpr
        let children : Array AstTree :=
          match innerT? with
          | none => #[]
          | some t => #[t]
        let trunc := t1 || innerT?.isNone
        (some { node := .proj structName.toString idx, children }, fuel, trunc)
  let (t?, _, trunc) := go maxNodes e
  let t := t?.getD { node := .other "empty", children := #[] }
  (t, trunc)

end HeytingLean.Embedding

