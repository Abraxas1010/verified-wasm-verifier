import Lean
import Std
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.AlgebraIR.Types

/-!
# HeytingLean.BountyHunter.AlgebraIR.Json

Deterministic JSON encoding/decoding for AlgebraIR graphs.

We use explicit `toJson` / `fromJsonE` functions (rather than implicit instances)
to keep the schema stable and the error messages human-friendly.
-/

namespace HeytingLean.BountyHunter.AlgebraIR

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

private def natArrayFromJsonE (j : Json) (ctx : String) : Except String (Array Nat) := do
  let a ← Internal.getArrE j ctx
  let rec go (xs : List Json) (acc : Array Nat) : Except String (Array Nat) := do
    match xs with
    | [] => pure acc
    | j :: js => go js (acc.push (← Internal.getNatE j s!"{ctx}[i]"))
  go a.toList #[]

def opToJson (o : Op) : Json :=
  Json.mkObj [("tag", Json.str o.tag)]

def effectToJson (e : Effect) : Json :=
  match e with
  | .storageRead slot =>
      Json.mkObj [("kind", Json.str "storageRead"), ("slot", Json.num (slot : Nat))]
  | .storageReadDyn slotExpr =>
      Json.mkObj [("kind", Json.str "storageReadDyn"), ("slotExpr", Json.str slotExpr)]
  | .storageWrite slot =>
      Json.mkObj [("kind", Json.str "storageWrite"), ("slot", Json.num (slot : Nat))]
  | .storageWriteDyn slotExpr =>
      Json.mkObj [("kind", Json.str "storageWriteDyn"), ("slotExpr", Json.str slotExpr)]
  | .boundaryCall target =>
      Json.mkObj [("kind", Json.str "boundaryCall"), ("target", Json.str target)]

def nodeToJson (n : Node) : Json :=
  Json.mkObj
    [ ("id", Json.num (n.id : Nat))
    , ("op", opToJson n.op)
    , ("args", Json.arr (n.args.map (fun (x : Nat) => Json.num x)))
    , ("effects", Json.arr (n.effects.map effectToJson))
    , ("succs", Json.arr (n.succs.map (fun (x : Nat) => Json.num x)))
    ]

def graphToJson (g : Graph) : Json :=
  Json.mkObj
    [ ("version", Json.str g.version)
    , ("entry", Json.num (g.entry : Nat))
    , ("exits", Json.arr (g.exits.map (fun (x : Nat) => Json.num x)))
    , ("nodes", Json.arr (g.nodes.map nodeToJson))
    ]

def graphToCanonicalString (g : Graph) : String :=
  HeytingLean.Util.JCS.canonicalString (graphToJson g)

def opFromJsonE (j : Json) : Except String Op := do
  let obj ← Internal.getObjE j "Op"
  let tagJ ← Internal.getObjValE obj "tag" "Op"
  let tag ← Internal.getStrE tagJ "Op.tag"
  pure { tag := tag }

def effectFromJsonE (j : Json) : Except String Effect := do
  let obj ← Internal.getObjE j "Effect"
  let kindJ ← Internal.getObjValE obj "kind" "Effect"
  let kind ← Internal.getStrE kindJ "Effect.kind"
  match kind with
  | "storageRead" =>
      let slotJ ← Internal.getObjValE obj "slot" "Effect.storageRead"
      pure (.storageRead (← Internal.getNatE slotJ "Effect.storageRead.slot"))
  | "storageReadDyn" =>
      let sJ ← Internal.getObjValE obj "slotExpr" "Effect.storageReadDyn"
      pure (.storageReadDyn (← Internal.getStrE sJ "Effect.storageReadDyn.slotExpr"))
  | "storageWrite" =>
      let slotJ ← Internal.getObjValE obj "slot" "Effect.storageWrite"
      pure (.storageWrite (← Internal.getNatE slotJ "Effect.storageWrite.slot"))
  | "storageWriteDyn" =>
      let sJ ← Internal.getObjValE obj "slotExpr" "Effect.storageWriteDyn"
      pure (.storageWriteDyn (← Internal.getStrE sJ "Effect.storageWriteDyn.slotExpr"))
  | "boundaryCall" =>
      let tJ ← Internal.getObjValE obj "target" "Effect.boundaryCall"
      pure (.boundaryCall (← Internal.getStrE tJ "Effect.boundaryCall.target"))
  | _ => .error s!"unknown Effect.kind '{kind}'"

def nodeFromJsonE (j : Json) : Except String Node := do
  let obj ← Internal.getObjE j "Node"
  let idJ ← Internal.getObjValE obj "id" "Node"
  let id ← Internal.getNatE idJ "Node.id"
  let opJ ← Internal.getObjValE obj "op" "Node"
  let op ← opFromJsonE opJ
  let parseNatArray (field : String) : Except String (Array Nat) := do
    match Internal.getObjValOpt obj field with
    | none => pure #[]
    | some j => natArrayFromJsonE j s!"Node.{field}"
  let args ← parseNatArray "args"
  let effects ←
    match Internal.getObjValOpt obj "effects" with
    | none => pure #[]
    | some eJ => do
        let a ← Internal.getArrE eJ "Node.effects"
        let rec go (xs : List Json) (acc : Array Effect) : Except String (Array Effect) := do
          match xs with
          | [] => pure acc
          | j :: js => go js (acc.push (← effectFromJsonE j))
        go a.toList #[]
  let succs ← parseNatArray "succs"
  pure { id := id, op := op, args := args, effects := effects, succs := succs }

def graphFromJsonE (j : Json) : Except String Graph := do
  let obj ← Internal.getObjE j "Graph"
  let version :=
    match Internal.getObjValOpt obj "version" with
    | some vJ =>
        match vJ.getStr? with
        | .ok s => s
        | .error _ => "algebrair.v1"
    | none => "algebrair.v1"
  let entryJ ← Internal.getObjValE obj "entry" "Graph"
  let entry ← Internal.getNatE entryJ "Graph.entry"
  let exits : Array NodeId ←
    match Internal.getObjValOpt obj "exits" with
    | none => pure #[]
    | some eJ => natArrayFromJsonE eJ "Graph.exits"
  let nodesJ ← Internal.getObjValE obj "nodes" "Graph"
  let nodesArr ← Internal.getArrE nodesJ "Graph.nodes"
  let rec go (xs : List Json) (acc : Array Node) : Except String (Array Node) := do
    match xs with
    | [] => pure acc
    | j :: js => go js (acc.push (← nodeFromJsonE j))
  let nodes ← go nodesArr.toList #[]
  pure { version := version, entry := entry, exits := exits, nodes := nodes }

def parseGraphStringE (s : String) : Except String Graph := do
  match Lean.Json.parse s with
  | .ok j =>
      graphFromJsonE j
  | .error e => .error s!"JSON parse error: {e}"

/-! ## Roundtrip helpers -/

/-- Print → parse roundtrip check using canonical JSON. -/
def graphRoundtripPrintParseOk (g : Graph) : Bool :=
  match parseGraphStringE (graphToCanonicalString g) with
  | .ok g' => g' = g
  | .error _ => false

/-- Parse → print → parse roundtrip check.

Returns the canonical string produced after parsing the input (so callers can
persist a normalized representation), plus a success flag indicating whether
the second parse reproduces the same `Graph`. -/
def graphRoundtripParsePrintParseE (raw : String) : Except String (String × Bool) := do
  let g ← parseGraphStringE raw
  let canon := graphToCanonicalString g
  let g2 ← parseGraphStringE canon
  pure (canon, g2 = g)

end HeytingLean.BountyHunter.AlgebraIR
