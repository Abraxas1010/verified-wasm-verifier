import Lean
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.Json

Deterministic JSON encoding helpers for the minimal Yul-text lexer/parser AST.

These are intended for *auditing* / debugging, not as a stable public schema.
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open Lean
open Lean.Json

def tokToJson (t : Tok) : Json :=
  match t with
  | .ident s => Json.mkObj [("kind", Json.str "ident"), ("s", Json.str s)]
  | .nat n => Json.mkObj [("kind", Json.str "nat"), ("n", Json.num n)]
  | .str s => Json.mkObj [("kind", Json.str "str"), ("s", Json.str s)]
  | .lparen => Json.mkObj [("kind", Json.str "lparen")]
  | .rparen => Json.mkObj [("kind", Json.str "rparen")]
  | .lbrace => Json.mkObj [("kind", Json.str "lbrace")]
  | .rbrace => Json.mkObj [("kind", Json.str "rbrace")]
  | .comma => Json.mkObj [("kind", Json.str "comma")]
  | .assignColonEq => Json.mkObj [("kind", Json.str "assignColonEq")]

def litToJson (l : Lit) : Json :=
  match l with
  | .nat n => Json.mkObj [("kind", Json.str "nat"), ("n", Json.num n)]
  | .str s => Json.mkObj [("kind", Json.str "str"), ("s", Json.str s)]
  | .bool b => Json.mkObj [("kind", Json.str "bool"), ("b", Json.bool b)]

partial def exprToJson (e : Expr) : Json :=
  match e with
  | .ident name => Json.mkObj [("kind", Json.str "ident"), ("name", Json.str name)]
  | .nat n => Json.mkObj [("kind", Json.str "nat"), ("n", Json.num n)]
  | .str s => Json.mkObj [("kind", Json.str "str"), ("s", Json.str s)]
  | .bool b => Json.mkObj [("kind", Json.str "bool"), ("b", Json.bool b)]
  | .call fn args =>
      Json.mkObj
        [ ("kind", Json.str "call")
        , ("fn", Json.str fn)
        , ("args", Json.arr (args.map exprToJson))
        ]

partial def stmtToJson (s : Stmt) : Json :=
  match s with
  | .let_ name rhs =>
      Json.mkObj [("kind", Json.str "let"), ("name", Json.str name), ("rhs", exprToJson rhs)]
  | .letMany names rhs =>
      Json.mkObj
        [ ("kind", Json.str "letMany")
        , ("names", Json.arr (names.map Json.str))
        , ("rhs", exprToJson rhs)
        ]
  | .assign name rhs =>
      Json.mkObj [("kind", Json.str "assign"), ("name", Json.str name), ("rhs", exprToJson rhs)]
  | .assignMany names rhs =>
      Json.mkObj
        [ ("kind", Json.str "assignMany")
        , ("names", Json.arr (names.map Json.str))
        , ("rhs", exprToJson rhs)
        ]
  | .expr e =>
      Json.mkObj [("kind", Json.str "expr"), ("expr", exprToJson e)]
  | .if_ cond thenStmts =>
      Json.mkObj
        [ ("kind", Json.str "if")
        , ("cond", exprToJson cond)
        , ("then", Json.arr (thenStmts.map stmtToJson))
        ]
  | .switch_ scrut cases default? =>
      let casesJ :=
        Json.arr <|
          cases.map (fun (c : Lit × Array Stmt) =>
            Json.mkObj
              [ ("lit", litToJson c.1)
              , ("body", Json.arr (c.2.map stmtToJson))
              ])
      let base :=
        [ ("kind", Json.str "switch")
        , ("scrut", exprToJson scrut)
        , ("cases", casesJ)
        ]
      let base :=
        match default? with
        | none => base
        | some ss => base ++ [("default", Json.arr (ss.map stmtToJson))]
      Json.mkObj base
  | .for_ init cond post body =>
      Json.mkObj
        [ ("kind", Json.str "for")
        , ("init", Json.arr (init.map stmtToJson))
        , ("cond", exprToJson cond)
        , ("post", Json.arr (post.map stmtToJson))
        , ("body", Json.arr (body.map stmtToJson))
        ]
  | .break => Json.mkObj [("kind", Json.str "break")]
  | .continue => Json.mkObj [("kind", Json.str "continue")]
  | .block ss =>
      Json.mkObj [("kind", Json.str "block"), ("stmts", Json.arr (ss.map stmtToJson))]
  | .return_ args =>
      let base := [("kind", Json.str "return")]
      let base :=
        if args.isEmpty then base else base ++ [("args", Json.arr (args.map exprToJson))]
      Json.mkObj base
  | .revert args =>
      let base := [("kind", Json.str "revert")]
      let base :=
        if args.isEmpty then base else base ++ [("args", Json.arr (args.map exprToJson))]
      Json.mkObj base
  | .leave => Json.mkObj [("kind", Json.str "leave")]

def stmtsToJson (ss : Array Stmt) : Json :=
  Json.arr (ss.map stmtToJson)

def toksToJson (ts : Array Tok) : Json :=
  Json.arr (ts.map tokToJson)

def toksRenderedToJson (ts : Array Tok) : Json :=
  Json.arr (ts.map (fun t => Json.str t.render))

def canonicalString (j : Json) : String :=
  HeytingLean.Util.JCS.canonicalString j

end HeytingLean.BountyHunter.Solc.YulTextMini
