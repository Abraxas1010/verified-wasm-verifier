import Lean
import Std.Data.HashSet
import HeytingLean.Embedding.Ast

namespace HeytingLean.Embedding

open Lean

private def litToString : Literal → String
  | .natVal n => s!"nat:{n}"
  | .strVal s => s!"str:{s}"

/-- Convert a Lean `Expr` into a JSON-serializable AST (with bounded node count). -/
partial def exprToAst (e : Expr) (maxNodes : Nat := 20000) : AstTree × Bool :=
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
      | .lam binderName type body _ =>
        let (tyT?, fuel, t1) := go (fuel - 1) type
        let (bodyT?, fuel, t2) := go fuel body
        let children : Array AstTree :=
          match tyT? with
          | none => #[]
          | some t => #[t]
        let children : Array AstTree :=
          match bodyT? with
          | none => children
          | some t => children.push t
        let trunc := t1 || t2 || tyT?.isNone || bodyT?.isNone
        (some { node := .lam binderName.toString, children }, fuel, trunc)
      | .forallE binderName type body _ =>
        let (tyT?, fuel, t1) := go (fuel - 1) type
        let (bodyT?, fuel, t2) := go fuel body
        let children : Array AstTree :=
          match tyT? with
          | none => #[]
          | some t => #[t]
        let children : Array AstTree :=
          match bodyT? with
          | none => children
          | some t => children.push t
        let trunc := t1 || t2 || tyT?.isNone || bodyT?.isNone
        (some { node := .forallE binderName.toString, children }, fuel, trunc)
      | .letE binderName type value body _ =>
        let (tyT?, fuel, t1) := go (fuel - 1) type
        let (valT?, fuel, t2) := go fuel value
        let (bodyT?, fuel, t3) := go fuel body
        let children : Array AstTree :=
          match tyT? with
          | none => #[]
          | some t => #[t]
        let children : Array AstTree :=
          match valT? with
          | none => children
          | some t => children.push t
        let children : Array AstTree :=
          match bodyT? with
          | none => children
          | some t => children.push t
        let trunc := t1 || t2 || t3 || tyT?.isNone || valT?.isNone || bodyT?.isNone
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

private def constNameToString (n : Name) : String :=
  n.toString

/-- Extract (deduped) constant names referenced by an `Expr`, with bounded traversal. -/
partial def exprToConstList (e : Expr) (maxNodes : Nat := 20000) (maxConsts : Nat := 2000) :
    Array String × Bool :=
  let rec go (fuel : Nat) (e : Expr) (seen : Std.HashSet String) (out : Array String) :
      Std.HashSet String × Array String × Nat × Bool :=
    if fuel = 0 then
      (seen, out, 0, true)
    else
      match e with
      | .mdata _ inner =>
        go fuel inner seen out
      | .bvar _ =>
        (seen, out, fuel - 1, false)
      | .fvar _ =>
        (seen, out, fuel - 1, false)
      | .mvar _ =>
        (seen, out, fuel - 1, false)
      | .sort _ =>
        (seen, out, fuel - 1, false)
      | .lit _ =>
        (seen, out, fuel - 1, false)
      | .const name _ =>
        let key := constNameToString name
        if out.size ≥ maxConsts then
          (seen, out, fuel - 1, true)
        else if seen.contains key then
          (seen, out, fuel - 1, false)
        else
          (seen.insert key, out.push key, fuel - 1, false)
      | .app fn arg =>
        let (seen, out, fuel, t1) := go (fuel - 1) fn seen out
        let (seen, out, fuel, t2) := go fuel arg seen out
        (seen, out, fuel, t1 || t2)
      | .lam _ type body _ =>
        let (seen, out, fuel, t1) := go (fuel - 1) type seen out
        let (seen, out, fuel, t2) := go fuel body seen out
        (seen, out, fuel, t1 || t2)
      | .forallE _ type body _ =>
        let (seen, out, fuel, t1) := go (fuel - 1) type seen out
        let (seen, out, fuel, t2) := go fuel body seen out
        (seen, out, fuel, t1 || t2)
      | .letE _ type value body _ =>
        let (seen, out, fuel, t1) := go (fuel - 1) type seen out
        let (seen, out, fuel, t2) := go fuel value seen out
        let (seen, out, fuel, t3) := go fuel body seen out
        (seen, out, fuel, t1 || t2 || t3)
      | .proj _ _ structExpr =>
        go (fuel - 1) structExpr seen out
  let seen0 : Std.HashSet String := Std.HashSet.emptyWithCapacity (min maxConsts 256)
  let (_, out, _, trunc) := go maxNodes e seen0 #[]
  (out, trunc)

end HeytingLean.Embedding
