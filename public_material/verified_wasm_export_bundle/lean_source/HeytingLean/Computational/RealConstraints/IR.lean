import Lean.Data.Json
import Std.Data.HashMap

namespace HeytingLean
namespace Computational
namespace RealConstraints

open Lean
open Lean.Json

structure VarDecl where
  name : String
  lo : Float
  hi : Float
deriving Repr, Inhabited

inductive Expr where
  | var (name : String)
  | const (value : Float)
  | add (children : Array Expr)
  | mul (children : Array Expr)
  | neg (child : Expr)
  | pow (base : Expr) (exp : Nat)
deriving Repr, Inhabited

inductive CmpOp where
  | lt | le | eq | ge | gt
deriving Repr, Inhabited

inductive Formula where
  | and (children : Array Formula)
  | or (children : Array Formula)
  | not (child : Formula)
  | cmp (op : CmpOp) (lhs : Expr) (rhs : Expr)
deriving Repr, Inhabited

structure Problem where
  vars : Array VarDecl
  formula : Formula
  precision : Float := 1e-3
deriving Repr, Inhabited

abbrev Env := Std.HashMap String Float

namespace JsonParse

private def expectObj (j : Json) : Except String Json := do
  match j.getObj? with
  | .ok _ => pure j
  | .error _ => throw "expected JSON object"

private def getStr (obj : Json) (k : String) : Except String String := do
  match obj.getObjVal? k with
  | .ok v =>
      match v.getStr? with
      | .ok s => pure s
      | .error _ => throw s!"field '{k}' not a string"
  | .error _ => throw s!"missing field '{k}'"

private def getNum (obj : Json) (k : String) : Except String Float := do
  match obj.getObjVal? k with
  | .ok v =>
      match v.getNum? with
      | .ok n => pure n.toFloat
      | .error _ => throw s!"field '{k}' not a number"
  | .error _ => throw s!"missing field '{k}'"

private def getNat (obj : Json) (k : String) : Except String Nat := do
  match obj.getObjVal? k with
  | .ok v =>
      match v.getInt? with
      | .ok i =>
          if i < 0 then
            throw s!"field '{k}' must be nonnegative"
          else
            pure i.toNat
      | .error _ => throw s!"field '{k}' not an integer"
  | .error _ => throw s!"missing field '{k}'"

private def getArr (obj : Json) (k : String) : Except String (Array Json) := do
  match obj.getObjVal? k with
  | .ok (Json.arr xs) => pure xs
  | .ok _ => throw s!"field '{k}' not an array"
  | .error _ => throw s!"missing field '{k}'"

private def getObjValOpt (obj : Json) (k : String) : Option Json :=
  match obj.getObjVal? k with
  | .ok v => some v
  | .error _ => none

end JsonParse

namespace VarDecl

def ofJson (j : Json) : Except String VarDecl := do
  let obj ← JsonParse.expectObj j
  let name ← JsonParse.getStr obj "name"
  let lo ← JsonParse.getNum obj "lo"
  let hi ← JsonParse.getNum obj "hi"
  if lo > hi then
    throw s!"var '{name}': lo > hi"
  pure { name, lo, hi }

end VarDecl

namespace Expr

partial def ofJson (j : Json) : Except String Expr := do
  let obj ← JsonParse.expectObj j
  let kind ← JsonParse.getStr obj "kind"
  match kind with
  | "var" =>
      let name ← JsonParse.getStr obj "name"
      pure (.var name)
  | "const" =>
      let v ← JsonParse.getNum obj "value"
      pure (.const v)
  | "add" =>
      let xs ← JsonParse.getArr obj "children"
      let mut out : Array Expr := #[]
      for x in xs do
        out := out.push (← Expr.ofJson x)
      pure (.add out)
  | "mul" =>
      let xs ← JsonParse.getArr obj "children"
      let mut out : Array Expr := #[]
      for x in xs do
        out := out.push (← Expr.ofJson x)
      pure (.mul out)
  | "neg" =>
      match JsonParse.getObjValOpt obj "child" with
      | none => throw "expr.neg missing field 'child'"
      | some ch => pure (.neg (← Expr.ofJson ch))
  | "pow" =>
      let base ←
        match JsonParse.getObjValOpt obj "base" with
        | none => throw "expr.pow missing field 'base'"
        | some b => Expr.ofJson b
      let exp ← JsonParse.getNat obj "exp"
      pure (.pow base exp)
  | _ =>
      throw s!"unknown expr kind: {kind}"

private def powNat (x : Float) (n : Nat) : Float :=
  -- Avoid depending on Float.pow semantics across toolchains.
  Nat.rec (motive := fun _ => Float) 1.0 (fun _ acc => acc * x) n

def eval (env : Env) : Expr → Except String Float
  | .var name =>
      match env.get? name with
      | some v => pure v
      | none => throw s!"unbound variable: {name}"
  | .const v => pure v
  | .add xs =>
      xs.foldlM (init := 0.0) (fun acc e => do pure (acc + (← eval env e)))
  | .mul xs =>
      xs.foldlM (init := 1.0) (fun acc e => do pure (acc * (← eval env e)))
  | .neg e => do pure (-(← eval env e))
  | .pow b n => do pure (powNat (← eval env b) n)

end Expr

namespace Formula

private def opOfString? (s : String) : Option CmpOp :=
  match s with
  | "<" => some .lt
  | "<=" => some .le
  | "=" => some .eq
  | "==" => some .eq
  | ">=" => some .ge
  | ">" => some .gt
  | _ => none

partial def ofJson (j : Json) : Except String Formula := do
  let obj ← JsonParse.expectObj j
  let kind ← JsonParse.getStr obj "kind"
  match kind with
  | "and" =>
      let xs ← JsonParse.getArr obj "children"
      let mut out : Array Formula := #[]
      for x in xs do
        out := out.push (← Formula.ofJson x)
      pure (.and out)
  | "or" =>
      let xs ← JsonParse.getArr obj "children"
      let mut out : Array Formula := #[]
      for x in xs do
        out := out.push (← Formula.ofJson x)
      pure (.or out)
  | "not" =>
      match JsonParse.getObjValOpt obj "child" with
      | none => throw "formula.not missing field 'child'"
      | some ch => pure (.not (← Formula.ofJson ch))
  | "cmp" =>
      let opStr ← JsonParse.getStr obj "op"
      let some op := opOfString? opStr
        | throw s!"formula.cmp: unsupported op '{opStr}'"
      let lhs ←
        match JsonParse.getObjValOpt obj "lhs" with
        | none => throw "formula.cmp missing field 'lhs'"
        | some e => Expr.ofJson e
      let rhs ←
        match JsonParse.getObjValOpt obj "rhs" with
        | none => throw "formula.cmp missing field 'rhs'"
        | some e => Expr.ofJson e
      pure (.cmp op lhs rhs)
  | _ =>
      throw s!"unknown formula kind: {kind}"

private def approxLe (a b eps : Float) : Bool :=
  a ≤ (b + eps)

private def approxLt (a b eps : Float) : Bool :=
  a < (b + eps)

private def approxGe (a b eps : Float) : Bool :=
  (a + eps) ≥ b

private def approxGt (a b eps : Float) : Bool :=
  (a + eps) > b

private def approxEq (a b eps : Float) : Bool :=
  let d := if a ≥ b then a - b else b - a
  d ≤ eps

def eval (env : Env) (eps : Float := 1e-6) : Formula → Except String Bool
  | .and xs =>
      xs.foldlM (init := true) (fun acc f => do
        if !acc then
          pure false
        else
          eval env eps f)
  | .or xs =>
      xs.foldlM (init := false) (fun acc f => do
        if acc then
          pure true
        else
          eval env eps f)
  | .not f => do pure (!(← eval env eps f))
  | .cmp op lhs rhs => do
      let a ← Expr.eval env lhs
      let b ← Expr.eval env rhs
      match op with
      | .le => pure <| approxLe a b eps
      | .lt => pure <| approxLt a b eps
      | .ge => pure <| approxGe a b eps
      | .gt => pure <| approxGt a b eps
      | .eq => pure <| approxEq a b eps

end Formula

namespace Problem

def ofJson (j : Json) : Except String Problem := do
  let obj ← JsonParse.expectObj j
  let varsJ ← JsonParse.getArr obj "vars"
  let mut vars : Array VarDecl := #[]
  for v in varsJ do
    vars := vars.push (← VarDecl.ofJson v)
  let formulaJ ←
    match obj.getObjVal? "formula" with
    | .ok v => pure v
    | .error _ => throw "missing field 'formula'"
  let formula ← Formula.ofJson formulaJ
  let mut prec : Float := 1e-3
  if let some cfgJ := JsonParse.getObjValOpt obj "config" then
    if let .ok cfgObj := cfgJ.getObj? then
      if let some pJ := cfgObj.get? "precision" then
        match pJ.getNum? with
        | .ok n => prec := n.toFloat
        | .error _ => throw "config.precision must be a number"
    else
      throw "config must be an object"
  pure { vars, formula, precision := prec }

def parseString (s : String) : Except String Problem := do
  match Json.parse s with
  | .ok j => ofJson j
  | .error e => throw s!"invalid JSON: {e}"

end Problem

end RealConstraints
end Computational
end HeytingLean
