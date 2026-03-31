import Lean
import Lean.Data.Json
import HeytingLean.CCI.Core

/-!
# JSON string encoders for CCI v1 (Lean‑side only)

We avoid depending on Lean’s internal Json object API; these are simple
string encoders sufficient for small exporters and tests.
-/

namespace HeytingLean
namespace CCI
open Lean

def jsonEscape (s : String) : String :=
  ((s.replace "\\" "\\\\").replace "\"" "\\\"")

private def q (s : String) : String := String.quote s

private def obj (kvs : List (String × String)) : String :=
  "{" ++ String.intercalate "," (kvs.map (fun (k,v) => q k ++ ":" ++ v)) ++ "}"

def encodeULevelStr : ULevel → String
  | .zero => obj [("tag", q "zero")]
  | .succ u => obj [("tag", q "succ"), ("u", encodeULevelStr u)]
  | .max a b => obj [("tag", q "max"), ("u", encodeULevelStr a), ("v", encodeULevelStr b)]
  | .imax a b => obj [("tag", q "imax"), ("u", encodeULevelStr a), ("v", encodeULevelStr b)]
  | .param n => obj [("tag", q "param"), ("name", q (jsonEscape n))]
  | .mvar n => obj [("tag", q "mvar"), ("name", q (jsonEscape n))]

def encodeBinderStyleStr : BinderStyle → String
  | .default => q "default"
  | .implicit => q "implicit"
  | .strictImplicit => q "strictImplicit"
  | .instImplicit => q "instImplicit"

def encodeLitValStr : LitVal → String
  | .nat n => obj [("tag", q "nat"), ("value", toString n)]
  | .str s => obj [("tag", q "str"), ("value", q (jsonEscape s))]

def encodeExprStr : Expr → String
  | Expr.atom id    => obj [("tag", q "atom"), ("id", q (jsonEscape id))]
  | Expr.andR a b   => obj [("tag", q "andR"), ("a", encodeExprStr a), ("b", encodeExprStr b)]
  | Expr.orR  a b   => obj [("tag", q "orR"),  ("a", encodeExprStr a), ("b", encodeExprStr b)]
  | Expr.impR a b   => obj [("tag", q "impR"), ("a", encodeExprStr a), ("b", encodeExprStr b)]
  | Expr.notR a     => obj [("tag", q "notR"), ("a", encodeExprStr a)]
  | Expr.bvar idx   => obj [("tag", q "bvar"), ("idx", toString idx)]
  | Expr.sort u     => obj [("tag", q "sort"), ("level", encodeULevelStr u)]
  | Expr.const n us =>
      obj
        [ ("tag", q "const")
        , ("name", q (jsonEscape n))
        , ("levels", "[" ++ String.intercalate "," (us.map encodeULevelStr) ++ "]")
        ]
  | Expr.app f a    => obj [("tag", q "app"), ("fn", encodeExprStr f), ("arg", encodeExprStr a)]
  | Expr.lam n bi ty body =>
      obj
        [ ("tag", q "lam")
        , ("binder", q (jsonEscape n))
        , ("binder_info", encodeBinderStyleStr bi)
        , ("type", encodeExprStr ty)
        , ("body", encodeExprStr body)
        ]
  | Expr.forallE n bi ty body =>
      obj
        [ ("tag", q "forallE")
        , ("binder", q (jsonEscape n))
        , ("binder_info", encodeBinderStyleStr bi)
        , ("type", encodeExprStr ty)
        , ("body", encodeExprStr body)
        ]
  | Expr.letE n ty val body =>
      obj
        [ ("tag", q "letE")
        , ("binder", q (jsonEscape n))
        , ("type", encodeExprStr ty)
        , ("value", encodeExprStr val)
        , ("body", encodeExprStr body)
        ]
  | Expr.lit v =>
      obj [("tag", q "lit"), ("lit", encodeLitValStr v)]
  | Expr.proj s idx body =>
      obj
        [ ("tag", q "proj")
        , ("struct", q (jsonEscape s))
        , ("idx", toString idx)
        , ("expr", encodeExprStr body)
        ]
  | Expr.fvar n => obj [("tag", q "fvar"), ("name", q (jsonEscape n))]
  | Expr.mvar n => obj [("tag", q "mvar"), ("name", q (jsonEscape n))]

def encodeLensStr (l : Lens) : String :=
  obj [("name", q (jsonEscape l.name)), ("value", q (jsonEscape l.value))]

/-- Decode universe levels from the JSON schema used by `encodeULevelStr`. -/
private partial def decodeULevel (j : Json) : Option ULevel :=
  match j.getObj? with
  | .error _ => none
  | .ok o =>
    let getTag? : Option String :=
      match o.get? "tag" with | some (.str s) => some s | _ => none
    match getTag? with
    | some "zero" => some .zero
    | some "succ" =>
        match o.get? "u" with
        | some ju => do
            let u ← decodeULevel ju
            some (.succ u)
        | _ => none
    | some "max" =>
        match (o.get? "u", o.get? "v") with
        | (some ju, some jv) => do
            let u ← decodeULevel ju
            let v ← decodeULevel jv
            some (.max u v)
        | _ => none
    | some "imax" =>
        match (o.get? "u", o.get? "v") with
        | (some ju, some jv) => do
            let u ← decodeULevel ju
            let v ← decodeULevel jv
            some (.imax u v)
        | _ => none
    | some "param" =>
        match o.get? "name" with
        | some (.str s) => some (.param s)
        | _ => none
    | some "mvar" =>
        match o.get? "name" with
        | some (.str s) => some (.mvar s)
        | _ => none
    | _ => none

private def decodeBinderStyle? : String → Option BinderStyle
  | "default" => some .default
  | "implicit" => some .implicit
  | "strictImplicit" => some .strictImplicit
  | "instImplicit" => some .instImplicit
  | _ => none

private def decodeLitVal (j : Json) : Option LitVal :=
  match j.getObj? with
  | .error _ => none
  | .ok o =>
    let getTag? : Option String :=
      match o.get? "tag" with | some (.str s) => some s | _ => none
    match getTag? with
    | some "nat" =>
        match o.get? "value" with
        | some n =>
            match n.getNat? with
            | .ok v => some (.nat v)
            | .error _ => none
        | _ => none
    | some "str" =>
        match o.get? "value" with
        | some (.str s) => some (.str s)
        | _ => none
    | _ => none

/-- Decode Expr from a Json object matching the encoder schema. -/
private def decodeExprFuel : Nat → Json → Option Expr
  | 0, _ => none
  | fuel + 1, j =>
      match j.getObj? with
      | .error _ => none
      | .ok o =>
        let getTag? : Option String :=
          match o.get? "tag" with | some (.str s) => some s | _ => none
        match getTag? with
        | some "atom" =>
            match o.get? "id" with
            | some (.str s) => some (.atom s)
            | _ => none
        | some "andR" =>
            match (o.get? "a", o.get? "b") with
            | (some ja, some jb) => do
                let a ← decodeExprFuel fuel ja
                let b ← decodeExprFuel fuel jb
                some (.andR a b)
            | _ => none
        | some "orR" =>
            match (o.get? "a", o.get? "b") with
            | (some ja, some jb) => do
                let a ← decodeExprFuel fuel ja
                let b ← decodeExprFuel fuel jb
                some (.orR a b)
            | _ => none
        | some "impR" =>
            match (o.get? "a", o.get? "b") with
            | (some ja, some jb) => do
                let a ← decodeExprFuel fuel ja
                let b ← decodeExprFuel fuel jb
                some (.impR a b)
            | _ => none
        | some "notR" =>
            match o.get? "a" with
            | some ja => do
                let a ← decodeExprFuel fuel ja
                some (.notR a)
            | _ => none
        | some "bvar" =>
            match o.get? "idx" with
            | some idx =>
                match idx.getNat? with
                | .ok i => some (.bvar i)
                | .error _ => none
            | _ => none
        | some "sort" =>
            match o.get? "level" with
            | some ju => do
                let u ← decodeULevel ju
                some (.sort u)
            | _ => none
        | some "const" =>
            match (o.get? "name", o.get? "levels") with
            | (some (.str n), some (.arr levels)) =>
                let rec go (xs : List Json) : Option (List ULevel) :=
                  match xs with
                  | [] => some []
                  | x :: rest => do
                      let u ← decodeULevel x
                      let us ← go rest
                      some (u :: us)
                do
                  let us ← go levels.toList
                  some (.const n us)
            | _ => none
        | some "app" =>
            match (o.get? "fn", o.get? "arg") with
            | (some jf, some ja) => do
                let f ← decodeExprFuel fuel jf
                let a ← decodeExprFuel fuel ja
                some (.app f a)
            | _ => none
        | some "lam" =>
            match (o.get? "binder", o.get? "binder_info", o.get? "type", o.get? "body") with
            | (some (.str n), some (.str bi), some jty, some jbody) => do
                let bi ← decodeBinderStyle? bi
                let ty ← decodeExprFuel fuel jty
                let body ← decodeExprFuel fuel jbody
                some (.lam n bi ty body)
            | _ => none
        | some "forallE" =>
            match (o.get? "binder", o.get? "binder_info", o.get? "type", o.get? "body") with
            | (some (.str n), some (.str bi), some jty, some jbody) => do
                let bi ← decodeBinderStyle? bi
                let ty ← decodeExprFuel fuel jty
                let body ← decodeExprFuel fuel jbody
                some (.forallE n bi ty body)
            | _ => none
        | some "letE" =>
            match (o.get? "binder", o.get? "type", o.get? "value", o.get? "body") with
            | (some (.str n), some jty, some jval, some jbody) => do
                let ty ← decodeExprFuel fuel jty
                let val ← decodeExprFuel fuel jval
                let body ← decodeExprFuel fuel jbody
                some (.letE n ty val body)
            | _ => none
        | some "lit" =>
            match o.get? "lit" with
            | some jlit => do
                let lit ← decodeLitVal jlit
                some (.lit lit)
            | _ => none
        | some "proj" =>
            match (o.get? "struct", o.get? "idx", o.get? "expr") with
            | (some (.str s), some idx, some jexpr) =>
                match idx.getNat? with
                | .ok i => do
                    let e ← decodeExprFuel fuel jexpr
                    some (.proj s i e)
                | .error _ => none
            | _ => none
        | some "fvar" =>
            match o.get? "name" with
            | some (.str s) => some (.fvar s)
            | _ => none
        | some "mvar" =>
            match o.get? "name" with
            | some (.str s) => some (.mvar s)
            | _ => none
        | _ => none

def decodeExpr (j : Json) : Option Expr :=
  decodeExprFuel 256 j

/-- Decode Expr from a String by parsing JSON first. -/
def decodeExprStr (s : String) : Option Expr :=
  match Json.parse s with
  | .ok j => decodeExpr j
  | .error _ => none

/-- Decode Lens from a Json object matching the encoder schema. -/
def decodeLens (j : Json) : Option Lens :=
  match j.getObj? with
  | .error _ => none
  | .ok o =>
    match (o.get? "name", o.get? "value") with
    | (some (.str n), some (.str v)) => some { name := n, value := v }
    | _ => none

end CCI
end HeytingLean
