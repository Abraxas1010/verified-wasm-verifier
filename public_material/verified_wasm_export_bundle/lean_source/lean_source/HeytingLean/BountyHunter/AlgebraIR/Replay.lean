import Lean
import Std
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.AlgebraIR.Types
import HeytingLean.BountyHunter.AlgebraIR.CEI
import HeytingLean.BountyHunter.AlgebraIR.Evidence
import HeytingLean.BountyHunter.AlgebraIR.Json

/-!
# HeytingLean.BountyHunter.AlgebraIR.Replay

Concrete-ish replay artifacts for AlgebraIR witnesses.

In Phase 2, we want a **saleable**, replayable artifact. Before we have a full EVM
stepper, the minimal replay spine is:

- a deterministic trace: a path of CFG node ids with the effects observed at each node
- a tiny replay checker that validates:
  - the path is a valid CFG walk
  - the CEI witness property holds on that trace (no `storageWrite(slot)` before `boundaryCall`)

This is intentionally *not* a full semantics; it is a bridging artifact that can be
lifted to CoreEVM / Foundry later.
-/

namespace HeytingLean.BountyHunter.AlgebraIR
namespace Replay

open Lean
open Lean.Json

structure Step where
  node : NodeId
  tag : String
  effects : Array Effect := #[]
  deriving Repr, DecidableEq, Inhabited

structure Trace where
  version : String := "algebrair.replay_trace.v0"
  path : Array Step := #[]
  deriving Repr, DecidableEq, Inhabited

def stepToJson (s : Step) : Json :=
  Json.mkObj
    [ ("node", Json.num s.node)
    , ("tag", Json.str s.tag)
    , ("effects", Json.arr (s.effects.map HeytingLean.BountyHunter.AlgebraIR.Evidence.effectToJson))
    ]

def traceToJson (t : Trace) : Json :=
  Json.mkObj
    [ ("version", Json.str t.version)
    , ("path", Json.arr (t.path.map stepToJson))
    ]

def traceCanonicalString (t : Trace) : String :=
  HeytingLean.Util.JCS.canonicalString (traceToJson t)

/-! ## JSON parsing -/

namespace JsonParse

private def orErr {α} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

def getObjE (j : Json) (ctx : String) : Except String (Std.TreeMap.Raw String Json compare) := do
  match j.getObj? with
  | .ok o => pure o
  | .error _ => .error s!"expected object ({ctx})"

def getArrE (j : Json) (ctx : String) : Except String (Array Json) := do
  match j.getArr? with
  | .ok a => pure a
  | .error _ => .error s!"expected array ({ctx})"

def getStrE (j : Json) (ctx : String) : Except String String := do
  match j.getStr? with
  | .ok s => pure s
  | .error _ => .error s!"expected string ({ctx})"

def getNatE (j : Json) (ctx : String) : Except String Nat := do
  match j.getNat? with
  | .ok n => pure n
  | .error _ => .error s!"expected Nat ({ctx})"

def getObjValE (obj : Std.TreeMap.Raw String Json compare) (k : String) (ctx : String) :
    Except String Json := do
  orErr (obj.get? k) s!"missing field '{k}' ({ctx})"

def getObjValOpt (obj : Std.TreeMap.Raw String Json compare) (k : String) : Option Json :=
  obj.get? k

end JsonParse

private def stepFromJsonE (j : Json) : Except String Step := do
  let obj ← JsonParse.getObjE j "Replay.Step"
  let nodeJ ← JsonParse.getObjValE obj "node" "Replay.Step"
  let tagJ ← JsonParse.getObjValE obj "tag" "Replay.Step"
  let node ← JsonParse.getNatE nodeJ "Replay.Step.node"
  let tag ← JsonParse.getStrE tagJ "Replay.Step.tag"
  let effs ←
    match JsonParse.getObjValOpt obj "effects" with
    | none => pure #[]
    | some eJ => do
        let a ← JsonParse.getArrE eJ "Replay.Step.effects"
        let rec go (xs : List Json) (acc : Array Effect) : Except String (Array Effect) := do
          match xs with
          | [] => pure acc
          | x :: xs => go xs (acc.push (← HeytingLean.BountyHunter.AlgebraIR.effectFromJsonE x))
        go a.toList #[]
  pure { node := node, tag := tag, effects := effs }

def traceFromJsonE (j : Json) : Except String Trace := do
  let obj ← JsonParse.getObjE j "Replay.Trace"
  let ver :=
    match JsonParse.getObjValOpt obj "version" with
    | none => "algebrair.replay_trace.v0"
    | some vJ =>
        match vJ.getStr? with
        | .ok s => s
        | .error _ => "algebrair.replay_trace.v0"
  let pathJ ← JsonParse.getObjValE obj "path" "Replay.Trace"
  let pathArr ← JsonParse.getArrE pathJ "Replay.Trace.path"
  let rec go (xs : List Json) (acc : Array Step) : Except String (Array Step) := do
    match xs with
    | [] => pure acc
    | x :: xs => go xs (acc.push (← stepFromJsonE x))
  let path ← go pathArr.toList #[]
  pure { version := ver, path := path }

private def nodeById? (g : Graph) (id : NodeId) : Option Node :=
  g.nodes.find? (fun n => n.id = id)

private def isEdge (g : Graph) (a b : NodeId) : Bool :=
  match nodeById? g a with
  | none => false
  | some n => n.succs.any (· = b)

private def stepOfNode (n : Node) : Step :=
  { node := n.id, tag := n.op.tag, effects := n.effects }

def traceFromPathE (g : Graph) (path : Array NodeId) : Except String Trace := do
  if path.isEmpty then
    throw "empty path"
  let mut steps : Array Step := #[]
  for id in path do
    match nodeById? g id with
    | none => throw s!"unknown node id in path: {id}"
    | some n => steps := steps.push (stepOfNode n)
  -- Validate edges.
  let mut i : Nat := 0
  while i + 1 < path.size do
    let a := path[i]!
    let b := path[i+1]!
    if !isEdge g a b then
      throw s!"invalid CFG edge in path: {a} -> {b}"
    i := i + 1
  return { path := steps }

def traceFromCEIWitnessE (g : Graph) (w : CEIWitness) : Except String Trace :=
  traceFromPathE g w.path

/-! ## Minimal replay checkers -/

private def hasBoundary (s : Step) : Bool :=
  s.effects.any (fun e => match e with | .boundaryCall _ => true | _ => false)

private def writesSlot (slot : Nat) (s : Step) : Bool :=
  s.effects.any (fun e => match e with | .storageWrite s' => s' = slot | _ => false)

/-- Replay-style validation of the CEI witness property. -/
def validateCEITrace (w : CEIWitness) (t : Trace) : Except String Unit := do
  let mut seenWrite := false
  for s in t.path do
    let writesThis :=
      match w.slotExpr? with
      | none => writesSlot w.slot s
      | some slotExpr =>
          s.effects.any (fun e => match e with | .storageWriteDyn se => se = slotExpr | _ => false)
    if writesThis then
      seenWrite := true
    if hasBoundary s then
      if seenWrite then
        throw "boundary reached after restore/write (not a CEI witness)"
      return ()
  throw "trace contains no boundaryCall effect"

/-- Validate and return `ok = true` iff the trace is a *witness* (bad ordering exists). -/
def replayCEIWitnessE (g : Graph) (w : CEIWitness) : Except String (Trace × Bool) := do
  let t ← traceFromCEIWitnessE g w
  match (validateCEITrace w t) with
  | .ok _ => return (t, true)
  | .error _ => return (t, false)

end Replay
end HeytingLean.BountyHunter.AlgebraIR
