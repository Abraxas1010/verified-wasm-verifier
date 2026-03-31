import Lean
import Lean.Data.Json
import HeytingLean.CLI.EnvBootstrap

open Lean

namespace HeytingLean.CLI.LeanExprJson

private def getNatVal (j : Json) (ctx : String) : Except String Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw s!"{ctx} is not a Nat"

private def nameFromString (text : String) : Name :=
  HeytingLean.CLI.EnvBootstrap.moduleNameFromString text

private def binderInfoToString : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private def binderInfoFromString? : String → Option BinderInfo
  | "default" => some .default
  | "implicit" => some .implicit
  | "strictImplicit" => some .strictImplicit
  | "instImplicit" => some .instImplicit
  | _ => none

partial def levelToJson : Level → Json
  | .zero => Json.mkObj [("tag", Json.str "zero")]
  | .succ u => Json.mkObj [("tag", Json.str "succ"), ("u", levelToJson u)]
  | .max u v => Json.mkObj [("tag", Json.str "max"), ("u", levelToJson u), ("v", levelToJson v)]
  | .imax u v => Json.mkObj [("tag", Json.str "imax"), ("u", levelToJson u), ("v", levelToJson v)]
  | .param n => Json.mkObj [("tag", Json.str "param"), ("name", Json.str n.toString)]
  | .mvar id => Json.mkObj [("tag", Json.str "mvar"), ("name", Json.str id.name.toString)]

partial def levelFromJson : Json → Except String Level
  | .obj fields => do
      let tag ←
        match fields.get? "tag" with
        | some (.str s) => pure s
        | _ => throw "level JSON is missing a string `tag`"
      match tag with
      | "zero" => pure .zero
      | "succ" =>
          match fields.get? "u" with
          | some u => return .succ (← levelFromJson u)
          | none => throw "level.succ is missing `u`"
      | "max" =>
          match fields.get? "u", fields.get? "v" with
          | some u, some v => return .max (← levelFromJson u) (← levelFromJson v)
          | _, _ => throw "level.max is missing `u` or `v`"
      | "imax" =>
          match fields.get? "u", fields.get? "v" with
          | some u, some v => return .imax (← levelFromJson u) (← levelFromJson v)
          | _, _ => throw "level.imax is missing `u` or `v`"
      | "param" =>
          match fields.get? "name" with
          | some (.str name) => pure (.param (nameFromString name))
          | _ => throw "level.param is missing string `name`"
      | "mvar" =>
          match fields.get? "name" with
          | some (.str name) => pure (.mvar { name := nameFromString name })
          | _ => throw "level.mvar is missing string `name`"
      | _ => throw s!"unknown level tag `{tag}`"
  | _ => throw "level JSON must be an object"

private def literalToJson : Literal → Json
  | .natVal n => Json.mkObj [("tag", Json.str "nat"), ("value", Json.num n)]
  | .strVal s => Json.mkObj [("tag", Json.str "str"), ("value", Json.str s)]

private def literalFromJson : Json → Except String Literal
  | .obj fields => do
      let tag ←
        match fields.get? "tag" with
        | some (.str s) => pure s
        | _ => throw "literal JSON is missing a string `tag`"
      match tag with
      | "nat" =>
          match fields.get? "value" with
          | some value => pure (.natVal (← getNatVal value "nat literal `value`"))
          | _ => throw "nat literal is missing numeric `value`"
      | "str" =>
          match fields.get? "value" with
          | some (.str s) => pure (.strVal s)
          | _ => throw "str literal is missing string `value`"
      | _ => throw s!"unknown literal tag `{tag}`"
  | _ => throw "literal JSON must be an object"

partial def exprToJson : Expr → Json
  | .bvar i =>
      Json.mkObj [("tag", Json.str "bvar"), ("idx", Json.num i)]
  | .sort u =>
      Json.mkObj [("tag", Json.str "sort"), ("level", levelToJson u)]
  | .const n us =>
      Json.mkObj
        [ ("tag", Json.str "const")
        , ("name", Json.str n.toString)
        , ("levels", Json.arr (us.toArray.map levelToJson))
        ]
  | .app f a =>
      Json.mkObj [("tag", Json.str "app"), ("fn", exprToJson f), ("arg", exprToJson a)]
  | .lam n ty body bi =>
      Json.mkObj
        [ ("tag", Json.str "lam")
        , ("binder", Json.str n.toString)
        , ("binder_info", Json.str (binderInfoToString bi))
        , ("type", exprToJson ty)
        , ("body", exprToJson body)
        ]
  | .forallE n ty body bi =>
      Json.mkObj
        [ ("tag", Json.str "forallE")
        , ("binder", Json.str n.toString)
        , ("binder_info", Json.str (binderInfoToString bi))
        , ("type", exprToJson ty)
        , ("body", exprToJson body)
        ]
  | .letE n ty val body _ =>
      Json.mkObj
        [ ("tag", Json.str "letE")
        , ("binder", Json.str n.toString)
        , ("type", exprToJson ty)
        , ("value", exprToJson val)
        , ("body", exprToJson body)
        ]
  | .lit lit =>
      Json.mkObj [("tag", Json.str "lit"), ("lit", literalToJson lit)]
  | .mdata _ body =>
      exprToJson body
  | .proj structName idx body =>
      Json.mkObj
        [ ("tag", Json.str "proj")
        , ("struct", Json.str structName.toString)
        , ("idx", Json.num idx)
        , ("expr", exprToJson body)
        ]
  | .fvar fvarId =>
      Json.mkObj [("tag", Json.str "fvar"), ("name", Json.str fvarId.name.toString)]
  | .mvar mvarId =>
      Json.mkObj [("tag", Json.str "mvar"), ("name", Json.str mvarId.name.toString)]

partial def exprFromJson : Json → Except String Expr
  | .obj fields => do
      let tag ←
        match fields.get? "tag" with
        | some (.str s) => pure s
        | _ => throw "expr JSON is missing a string `tag`"
      match tag with
      | "bvar" =>
          match fields.get? "idx" with
          | some j => pure (.bvar (← getNatVal j "bvar `idx`"))
          | _ => throw "bvar is missing numeric `idx`"
      | "sort" =>
          match fields.get? "level" with
          | some lvl => return .sort (← levelFromJson lvl)
          | none => throw "sort is missing `level`"
      | "const" =>
          match fields.get? "name", fields.get? "levels" with
          | some (.str name), some (.arr levels) =>
              let mut us : List Level := []
              for levelJson in levels.toList.reverse do
                us := (← levelFromJson levelJson) :: us
              pure (.const (nameFromString name) us)
          | _, _ => throw "const is missing `name` or `levels`"
      | "app" =>
          match fields.get? "fn", fields.get? "arg" with
          | some fn, some arg => return .app (← exprFromJson fn) (← exprFromJson arg)
          | _, _ => throw "app is missing `fn` or `arg`"
      | "lam" =>
          match fields.get? "binder", fields.get? "binder_info", fields.get? "type", fields.get? "body" with
          | some (.str binder), some (.str bi), some ty, some body =>
              let some binderInfo := binderInfoFromString? bi
                | throw s!"unknown binder_info `{bi}`"
              return .lam (nameFromString binder) (← exprFromJson ty) (← exprFromJson body) binderInfo
          | _, _, _, _ => throw "lam is missing `binder`, `binder_info`, `type`, or `body`"
      | "forallE" =>
          match fields.get? "binder", fields.get? "binder_info", fields.get? "type", fields.get? "body" with
          | some (.str binder), some (.str bi), some ty, some body =>
              let some binderInfo := binderInfoFromString? bi
                | throw s!"unknown binder_info `{bi}`"
              return .forallE (nameFromString binder) (← exprFromJson ty) (← exprFromJson body) binderInfo
          | _, _, _, _ => throw "forallE is missing `binder`, `binder_info`, `type`, or `body`"
      | "letE" =>
          match fields.get? "binder", fields.get? "type", fields.get? "value", fields.get? "body" with
          | some (.str binder), some ty, some val, some body =>
              return .letE (nameFromString binder) (← exprFromJson ty) (← exprFromJson val) (← exprFromJson body) false
          | _, _, _, _ => throw "letE is missing `binder`, `type`, `value`, or `body`"
      | "lit" =>
          match fields.get? "lit" with
          | some lit => return .lit (← literalFromJson lit)
          | none => throw "lit is missing `lit`"
      | "proj" =>
          match fields.get? "struct", fields.get? "idx", fields.get? "expr" with
          | some (.str structName), some idx, some body =>
              return .proj (nameFromString structName) (← getNatVal idx "proj `idx`") (← exprFromJson body)
          | _, _, _ => throw "proj is missing `struct`, `idx`, or `expr`"
      | "fvar" =>
          match fields.get? "name" with
          | some (.str name) => pure (.fvar { name := nameFromString name })
          | _ => throw "fvar is missing string `name`"
      | "mvar" =>
          match fields.get? "name" with
          | some (.str name) => pure (.mvar { name := nameFromString name })
          | _ => throw "mvar is missing string `name`"
      | _ => throw s!"unknown expr tag `{tag}`"
  | _ => throw "expr JSON must be an object"

end HeytingLean.CLI.LeanExprJson
