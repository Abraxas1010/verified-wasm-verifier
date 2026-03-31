import Lean
import Std
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.YulMini.Types

/-!
# HeytingLean.BountyHunter.YulMini.Json

Deterministic JSON encoding/decoding for the YulMini AST.
-/

namespace HeytingLean.BountyHunter.YulMini

open Lean
open Lean.Json

namespace Internal

private def orErr {α} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

private def getObjE (j : Json) (ctx : String) : Except String (Std.TreeMap.Raw String Json compare) := do
  match j.getObj? with
  | .ok o => pure o
  | .error _ => .error s!"expected object ({ctx})"

private def getArrE (j : Json) (ctx : String) : Except String (Array Json) := do
  match j.getArr? with
  | .ok a => pure a
  | .error _ => .error s!"expected array ({ctx})"

private def getStrE (j : Json) (ctx : String) : Except String String := do
  match j.getStr? with
  | .ok s => pure s
  | .error _ => .error s!"expected string ({ctx})"

private def getNatE (j : Json) (ctx : String) : Except String Nat := do
  match j.getNat? with
  | .ok n => pure n
  | .error _ => .error s!"expected Nat ({ctx})"

private def getObjValE (obj : Std.TreeMap.Raw String Json compare) (k : String) (ctx : String) :
    Except String Json := do
  orErr (obj.get? k) s!"missing field '{k}' ({ctx})"

private def getObjValOpt (obj : Std.TreeMap.Raw String Json compare) (k : String) : Option Json :=
  obj.get? k

end Internal

def builtinToJson (b : Builtin) : Json :=
  match b with
  | .sload slot =>
      Json.mkObj [("kind", Json.str "sload"), ("slot", Json.num slot)]
  | .sstore slot =>
      Json.mkObj [("kind", Json.str "sstore"), ("slot", Json.num slot)]
  | .call target =>
      Json.mkObj [("kind", Json.str "call"), ("target", Json.str target)]

def exprToJson (e : Expr) : Json :=
  match e with
  | .var x => Json.mkObj [("kind", Json.str "var"), ("name", Json.str x)]
  | .nat n => Json.mkObj [("kind", Json.str "nat"), ("value", Json.num n)]
  | .builtin b args =>
      Json.mkObj
        [ ("kind", Json.str "builtin")
        , ("builtin", builtinToJson b)
        , ("args", Json.arr (args.map exprToJson))
        ]

def stmtToJson (s : Stmt) : Json :=
  match s with
  | .let_ x e =>
      Json.mkObj [("kind", Json.str "let"), ("name", Json.str x), ("expr", exprToJson e)]
  | .expr e =>
      Json.mkObj [("kind", Json.str "expr"), ("expr", exprToJson e)]
  | .if_ c t e =>
      Json.mkObj
        [ ("kind", Json.str "if")
        , ("cond", exprToJson c)
        , ("then", Json.arr (t.map stmtToJson))
        , ("else", Json.arr (e.map stmtToJson))
        ]
  | .return_ =>
      Json.mkObj [("kind", Json.str "return")]
  | .revert =>
      Json.mkObj [("kind", Json.str "revert")]

def funcToJson (f : Func) : Json :=
  Json.mkObj
    [ ("name", Json.str f.name)
    , ("body", Json.arr (f.body.map stmtToJson))
    ]

def programToJson (p : Program) : Json :=
  Json.mkObj
    [ ("version", Json.str p.version)
    , ("funcs", Json.arr (p.funcs.map funcToJson))
    ]

def programToCanonicalString (p : Program) : String :=
  HeytingLean.Util.JCS.canonicalString (programToJson p)

def builtinFromJsonE (j : Json) : Except String Builtin := do
  let obj ← Internal.getObjE j "Builtin"
  let kJ ← Internal.getObjValE obj "kind" "Builtin"
  let k ← Internal.getStrE kJ "Builtin.kind"
  match k with
  | "sload" =>
      let slotJ ← Internal.getObjValE obj "slot" "Builtin.sload"
      pure (.sload (← Internal.getNatE slotJ "Builtin.sload.slot"))
  | "sstore" =>
      let slotJ ← Internal.getObjValE obj "slot" "Builtin.sstore"
      pure (.sstore (← Internal.getNatE slotJ "Builtin.sstore.slot"))
  | "call" =>
      let tJ ← Internal.getObjValE obj "target" "Builtin.call"
      pure (.call (← Internal.getStrE tJ "Builtin.call.target"))
  | _ => .error s!"unknown Builtin.kind '{k}'"

partial def exprFromJsonE (j : Json) : Except String Expr := do
  let obj ← Internal.getObjE j "Expr"
  let kJ ← Internal.getObjValE obj "kind" "Expr"
  let k ← Internal.getStrE kJ "Expr.kind"
  match k with
  | "var" =>
      let nJ ← Internal.getObjValE obj "name" "Expr.var"
      pure (.var (← Internal.getStrE nJ "Expr.var.name"))
  | "nat" =>
      let vJ ← Internal.getObjValE obj "value" "Expr.nat"
      pure (.nat (← Internal.getNatE vJ "Expr.nat.value"))
  | "builtin" =>
      let bJ ← Internal.getObjValE obj "builtin" "Expr.builtin"
      let b ← builtinFromJsonE bJ
      let args ←
        match Internal.getObjValOpt obj "args" with
        | none => pure #[]
        | some aJ =>
            let arr ← Internal.getArrE aJ "Expr.builtin.args"
            let rec go (xs : List Json) (acc : Array Expr) : Except String (Array Expr) := do
              match xs with
              | [] => pure acc
              | j :: js => go js (acc.push (← exprFromJsonE j))
            go arr.toList #[]
      pure (.builtin b args)
  | _ => .error s!"unknown Expr.kind '{k}'"

partial def stmtFromJsonE (j : Json) : Except String Stmt := do
  let obj ← Internal.getObjE j "Stmt"
  let kJ ← Internal.getObjValE obj "kind" "Stmt"
  let k ← Internal.getStrE kJ "Stmt.kind"
  match k with
  | "let" =>
      let nJ ← Internal.getObjValE obj "name" "Stmt.let"
      let eJ ← Internal.getObjValE obj "expr" "Stmt.let"
      pure (.let_ (← Internal.getStrE nJ "Stmt.let.name") (← exprFromJsonE eJ))
  | "expr" =>
      let eJ ← Internal.getObjValE obj "expr" "Stmt.expr"
      pure (.expr (← exprFromJsonE eJ))
  | "if" =>
      let cJ ← Internal.getObjValE obj "cond" "Stmt.if"
      let tJ ← Internal.getObjValE obj "then" "Stmt.if"
      let eJ := Internal.getObjValOpt obj "else" |>.getD (Json.arr #[])
      let tArr ← Internal.getArrE tJ "Stmt.if.then"
      let eArr ← Internal.getArrE eJ "Stmt.if.else"
      let rec go (xs : List Json) (acc : Array Stmt) : Except String (Array Stmt) := do
        match xs with
        | [] => pure acc
        | j :: js => go js (acc.push (← stmtFromJsonE j))
      let thenStmts ← go tArr.toList #[]
      let elseStmts ← go eArr.toList #[]
      pure (.if_ (← exprFromJsonE cJ) thenStmts elseStmts)
  | "return" => pure .return_
  | "revert" => pure .revert
  | _ => .error s!"unknown Stmt.kind '{k}'"

def funcFromJsonE (j : Json) : Except String Func := do
  let obj ← Internal.getObjE j "Func"
  let nJ ← Internal.getObjValE obj "name" "Func"
  let bJ ← Internal.getObjValE obj "body" "Func"
  let name ← Internal.getStrE nJ "Func.name"
  let arr ← Internal.getArrE bJ "Func.body"
  let rec go (xs : List Json) (acc : Array Stmt) : Except String (Array Stmt) := do
    match xs with
    | [] => pure acc
    | j :: js => go js (acc.push (← stmtFromJsonE j))
  pure { name := name, body := (← go arr.toList #[]) }

def programFromJsonE (j : Json) : Except String Program := do
  let obj ← Internal.getObjE j "Program"
  let version :=
    match Internal.getObjValOpt obj "version" with
    | some vJ =>
        match vJ.getStr? with | .ok s => s | .error _ => "yulmini.v1"
    | none => "yulmini.v1"
  let fJ ← Internal.getObjValE obj "funcs" "Program"
  let arr ← Internal.getArrE fJ "Program.funcs"
  let rec go (xs : List Json) (acc : Array Func) : Except String (Array Func) := do
    match xs with
    | [] => pure acc
    | j :: js => go js (acc.push (← funcFromJsonE j))
  pure { version := version, funcs := (← go arr.toList #[]) }

def parseProgramStringE (s : String) : Except String Program := do
  match Lean.Json.parse s with
  | .ok j => programFromJsonE j
  | .error e => .error s!"JSON parse error: {e}"

/-! ## Roundtrip helpers -/

def programRoundtripPrintParseOk (p : Program) : Bool :=
  match parseProgramStringE (programToCanonicalString p) with
  | .ok p' => programToJson p' == programToJson p
  | .error _ => false

def programRoundtripParsePrintParseE (raw : String) : Except String (String × Bool) := do
  let p ← parseProgramStringE raw
  let canon := programToCanonicalString p
  let p2 ← parseProgramStringE canon
  pure (canon, programToJson p2 == programToJson p)

end HeytingLean.BountyHunter.YulMini
