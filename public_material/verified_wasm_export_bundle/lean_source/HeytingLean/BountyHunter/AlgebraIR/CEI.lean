import Lean
import Std
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.AlgebraIR.Types
import HeytingLean.BountyHunter.AlgebraIR.Dominators
import HeytingLean.BountyHunter.AlgebraIR.SlotRef

/-!
# HeytingLean.BountyHunter.AlgebraIR.CEI

Phase 0 “choke point” check: dominance-style **boundary restoration**.

For reentrancy/CEI, the key safety obligation is:

> A storage write that restores an invariant must dominate any boundary call.

We start with the simplest concrete instance:

- boundary = `Effect.boundaryCall _`
- restore/write = `Effect.storageWrite slot`
- obligation = “∃ write(slot) that dominates boundary”
-/

namespace HeytingLean.BountyHunter.AlgebraIR

open Lean
open Lean.Json

inductive Verdict where
  | safe
  | vulnerable
  | outOfScope (reason : String)
  deriving Repr, DecidableEq, Inhabited

structure CEIWitness where
  version : String := "cei_witness.v2"
  boundaryNode : NodeId
  slot : Nat
  slotExpr? : Option String := none
  /-- A concrete CFG path from `entry` to `boundaryNode` that avoids any `storageWrite(slot)`. -/
  path : Array NodeId := #[]
  reason : String
  deriving Repr, DecidableEq, Inhabited

def verdictToJson (v : Verdict) : Json :=
  match v with
  | .safe => Json.mkObj [("verdict", Json.str "SAFE")]
  | .vulnerable => Json.mkObj [("verdict", Json.str "VULNERABLE")]
  | .outOfScope r => Json.mkObj [("verdict", Json.str "OUT_OF_SCOPE"), ("reason", Json.str r)]

def ceiWitnessToJson (w : CEIWitness) : Json :=
  let base :=
    [ ("version", Json.str w.version)
    , ("boundaryNode", Json.num w.boundaryNode)
    , ("slot", Json.num w.slot)
    , ("path", Json.arr (w.path.map (fun (x : Nat) => Json.num x)))
    , ("reason", Json.str w.reason)
    ]
  let base :=
    match w.slotExpr? with
    | none => base
    | some s => base ++ [("slotExpr", Json.str s)]
  Json.mkObj base

def verdictBundleToJson (v : Verdict) (w? : Option CEIWitness := none) : Json :=
  match w? with
  | none => verdictToJson v
  | some w =>
      match verdictToJson v with
      | .obj kvs =>
          Json.obj (kvs.insert "witness" (ceiWitnessToJson w))
      | other => other

def verdictBundleCanonicalString (v : Verdict) (w? : Option CEIWitness := none) : String :=
  HeytingLean.Util.JCS.canonicalString (verdictBundleToJson v w?)

private def hasBoundary (n : Node) : Bool :=
  n.effects.any (fun e => match e with | .boundaryCall _ => true | _ => false)

private def writesSlot (slot : Nat) (n : Node) : Bool :=
  n.effects.any (fun e => match e with | .storageWrite s => s = slot | _ => false)

private def hasDynWrite (n : Node) : Bool :=
  n.effects.any (fun e => match e with | .storageWriteDyn _ => true | _ => false)

private def slotRefMatches (sel obs : HeytingLean.BountyHunter.AlgebraIR.SlotRef) : Bool :=
  match sel, obs with
  | .packed selBase selOff selSz, .packed obsBase obsOff obsSz =>
      selBase = obsBase && selOff = obsOff && selSz = obsSz
  | .packed selBase _ _, _ =>
      obs = selBase
  | _, .packed obsBase _ _ =>
      sel = obsBase
  | _, _ =>
      sel = obs

private def writesDynRef (slotRef : HeytingLean.BountyHunter.AlgebraIR.SlotRef) (n : Node) : Bool :=
  n.effects.any (fun e =>
    match e with
    | .storageWriteDyn s =>
        match HeytingLean.BountyHunter.AlgebraIR.slotRefParse? s with
        | none => false
        | some r => slotRefMatches slotRef r
    | _ => false)

private def hasUnknownDynWrite (n : Node) : Bool :=
  n.effects.any (fun e =>
    match e with
    | .storageWriteDyn s => HeytingLean.BountyHunter.AlgebraIR.slotRefParse? s |>.isNone
    | _ => false)

private def boundaryTargets (g : Graph) : Array NodeId :=
  g.nodes.foldl (fun acc n => if hasBoundary n then acc.push n.id else acc) #[]

private def writeNodesFor (g : Graph) (slot : Nat) : Array NodeId :=
  g.nodes.foldl (fun acc n => if writesSlot slot n then acc.push n.id else acc) #[]

private def isWriteNode (g : Graph) (slot : Nat) (id : NodeId) : Bool :=
  match g.nodes.find? (fun n => n.id = id) with
  | none => false
  | some n => writesSlot slot n || hasDynWrite n

private def isWriteNodeDyn (g : Graph) (slotRef : HeytingLean.BountyHunter.AlgebraIR.SlotRef) (id : NodeId) : Bool :=
  match g.nodes.find? (fun n => n.id = id) with
  | none => false
  | some n => writesDynRef slotRef n || hasUnknownDynWrite n

private def succsOf (g : Graph) (id : NodeId) : Array NodeId :=
  match g.nodes.find? (fun n => n.id = id) with
  | none => #[]
  | some n => n.succs

private def reconstructPath (pred : Std.HashMap NodeId NodeId) (start target : NodeId) :
    Option (Array NodeId) :=
  Id.run do
    let mut cur := target
    let mut acc : List NodeId := [target]
    let mut fuel : Nat := pred.size + 2
    while fuel > 0 && cur ≠ start do
      fuel := fuel - 1
      match pred.get? cur with
      | none => return none
      | some p =>
          acc := p :: acc
          cur := p
    if cur = start then
      return some acc.toArray
    else
      return none

private def findPathAvoidingWrites (g : Graph) (slot : Nat) (target : NodeId) :
    Option (Array NodeId) :=
  if isWriteNode g slot g.entry then
    none
  else
    Id.run do
      let mut visited : Std.HashSet NodeId := Std.HashSet.emptyWithCapacity (g.nodes.size + 1)
      let mut pred : Std.HashMap NodeId NodeId := Std.HashMap.emptyWithCapacity (g.nodes.size + 1)
      let mut q : List NodeId := [g.entry]
      visited := visited.insert g.entry
      let mut fuel : Nat := g.nodes.size * 4 + 10
      while fuel > 0 do
        fuel := fuel - 1
        match q with
        | [] => return none
        | v :: rest =>
            q := rest
            if v = target then
              return reconstructPath pred g.entry target
            for s in succsOf g v do
              if isWriteNode g slot s then
                continue
              if !visited.contains s then
                visited := visited.insert s
                pred := pred.insert s v
                q := q ++ [s]
      return none

private def findPathAvoidingWritesDyn (g : Graph) (slotRef : HeytingLean.BountyHunter.AlgebraIR.SlotRef) (target : NodeId) :
    Option (Array NodeId) :=
  if isWriteNodeDyn g slotRef g.entry then
    none
  else
    Id.run do
      let mut visited : Std.HashSet NodeId := Std.HashSet.emptyWithCapacity (g.nodes.size + 1)
      let mut pred : Std.HashMap NodeId NodeId := {}
      let mut q : Std.Queue NodeId := Std.Queue.empty
      visited := visited.insert g.entry
      q := q.enqueue g.entry
      let mut fuel : Nat := g.nodes.size * 10 + 10
      while fuel > 0 do
        fuel := fuel - 1
        match q.dequeue? with
        | none => break
        | some (cur, q2) =>
            q := q2
            if cur = target then
              return reconstructPath pred g.entry target
            for s in succsOf g cur do
              if !visited.contains s then
                if isWriteNodeDyn g slotRef s then
                  continue
                visited := visited.insert s
                pred := pred.insert s cur
                q := q.enqueue s
      return none

/-- Pick a “best-effort” dynamic slot expression to check.

Current heuristic (deterministic): first `storageWriteDyn` payload in node order
that parses as a supported `SlotRef`. -/
def pickAutoSlotExpr? (g : Graph) : Option String :=
  g.nodes.toList.findSome? (fun n =>
    n.effects.toList.findSome? (fun e =>
      match e with
      | .storageWriteDyn s => if HeytingLean.BountyHunter.AlgebraIR.slotRefParse? s |>.isSome then some s else none
      | _ => none))

/-- Pick a “best-effort” concrete storage slot to check.

Current heuristic (deterministic): first `storageWrite(slot)` in node order. -/
def pickAutoSlot? (g : Graph) : Option Nat :=
  g.nodes.toList.findSome? (fun n =>
    n.effects.toList.findSome? (fun e =>
      match e with
      | .storageWrite slot => some slot
      | _ => none))

/-- CEI check for a single `slot`.

Returns:
- `.safe` if there is no path to any boundary that avoids `storageWrite(slot)`.
- `.vulnerable` with a concrete counterexample path otherwise.
- `.outOfScope` if the graph has no boundaries (nothing to check).
-/
def checkCEI (g : Graph) (slot : Nat) : Verdict × Option CEIWitness :=
  let boundaries := boundaryTargets g
  if boundaries.isEmpty then
    (.outOfScope "no boundaryCall effects in graph", none)
  else
    let firstFail : Option (NodeId × Array NodeId) :=
      boundaries.toList.findSome? (fun b =>
        match findPathAvoidingWrites g slot b with
        | none => none
        | some p => some (b, p))
    match firstFail with
    | none =>
        if g.nodes.any hasDynWrite then
          (.outOfScope "dynamic storage writes present; cannot certify CEI safety for a concrete slot", none)
        else
          (.safe, none)
    | some (b, p) =>
        (.vulnerable, some
          { boundaryNode := b
            slot := slot
            path := p
            reason := s!"found path to boundary avoiding storageWrite({slot})" })

def checkCEISlotExpr (g : Graph) (slotExpr : String) : Verdict × Option CEIWitness :=
  let boundaries := boundaryTargets g
  if boundaries.isEmpty then
    (.outOfScope "no boundaryCall effects in graph", none)
  else
    let slotRef? := HeytingLean.BountyHunter.AlgebraIR.slotRefParse? slotExpr
    match slotRef? with
    | none => (.outOfScope s!"slotExpr not supported: {slotExpr}", none)
    | some slotRef =>
        let firstFail : Option (NodeId × Array NodeId) :=
          boundaries.toList.findSome? (fun b =>
            match findPathAvoidingWritesDyn g slotRef b with
            | none => none
            | some p => some (b, p))
        match firstFail with
        | none =>
            if g.nodes.any hasUnknownDynWrite then
              (.outOfScope "unknown dynamic storage writes present; cannot certify CEI safety for slotExpr", none)
            else
              (.safe, none)
        | some (b, p) =>
            (.vulnerable, some
              { boundaryNode := b
                slot := 0
                slotExpr? := some slotExpr
                path := p
                reason := s!"found path to boundary avoiding storageWriteDyn({slotExpr})" })

end HeytingLean.BountyHunter.AlgebraIR
