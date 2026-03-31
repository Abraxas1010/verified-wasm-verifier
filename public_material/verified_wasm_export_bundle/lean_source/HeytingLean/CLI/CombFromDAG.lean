import Lean.Data.Json
import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Combinators.SKYMachineBounded

/-!
# CombFromDAG — Phase 4b of ProofBreeder Interactive Construction

Reconstruct a `Comb` tree from a shared-heap DAG representation (the inverse of
`SKYMachineBounded.State.compileComb?`). Fuel-limited with memoization to avoid
exponential blowup on highly shared DAGs.
-/

open Lean

namespace HeytingLean.CLI.CombFromDAG

open HeytingLean.LoF
open HeytingLean.LoF.Combinators

/-- Reconstruct a Comb tree from a shared-heap DAG representation.
    Uses memoization (HashMap) to avoid exponential blowup on shared nodes.
    Fuel-limited to prevent infinite loops on cyclic/corrupt input. -/
partial def heapToCombMemo (nodes : Array (SKYGraph.Node Unit)) (focus : Nat)
    (memo : Std.HashMap Nat Comb) (fuel : Nat) : Except String (Comb × Std.HashMap Nat Comb) := do
  if fuel == 0 then throw "fuel exhausted in heapToComb"
  match memo.get? focus with
  | some c => .ok (c, memo)
  | none =>
    if h : focus < nodes.size then
      match nodes[focus] with
      | .combK => let c := Comb.K; .ok (c, memo.insert focus c)
      | .combS => let c := Comb.S; .ok (c, memo.insert focus c)
      | .combY => let c := Comb.Y; .ok (c, memo.insert focus c)
      | .oracle _ => throw "oracle nodes cannot be decompiled"
      | .app f a =>
          let (fc, memo') ← heapToCombMemo nodes f memo (fuel - 1)
          let (ac, memo'') ← heapToCombMemo nodes a memo' (fuel - 1)
          let c := Comb.app fc ac
          .ok (c, memo''.insert focus c)
    else throw s!"focus {focus} out of bounds (size {nodes.size})"

/-- Reconstruct a Comb tree from a shared-heap DAG. Convenience wrapper. -/
def heapToComb (nodes : Array (SKYGraph.Node Unit)) (focus : Nat)
    (fuel : Nat := 100000) : Except String Comb := do
  let (c, _) ← heapToCombMemo nodes focus {} fuel
  return c

/-- Parse a single JSON node to SKYGraph.Node Unit. -/
private def parseJsonNode (j : Json) : Except String (SKYGraph.Node Unit) := do
  let tag ← j.getObjValAs? String "tag"
  match tag with
  | "K" => .ok .combK
  | "S" => .ok .combS
  | "Y" => .ok .combY
  | "oracle" => .ok (.oracle ())
  | "app" =>
      let f ← j.getObjValAs? Nat "f"
      let a ← j.getObjValAs? Nat "a"
      .ok (.app f a)
  | other => throw s!"unknown node tag: {other}"

/-- Parse a JSON SKY machine state back to Comb.
    Expected format: { "nodes": [...], "focus": N, ... } -/
def jsonToComb (j : Json) : Except String Comb := do
  let nodesArr ← j.getObjValAs? (Array Json) "nodes"
  let focus ← j.getObjValAs? Nat "focus"
  let mut nodes : Array (SKYGraph.Node Unit) := #[]
  for nodeJson in nodesArr do
    let node ← parseJsonNode nodeJson
    nodes := nodes.push node
  heapToComb nodes focus

/-- Roundtrip test: compile a Comb to machine state, then reconstruct.
    Returns true iff the roundtrip produces a structurally equal Comb. -/
def roundtripTest (maxNodes : Nat) (c : Comb) : Bool :=
  match SKYMachineBounded.State.compileComb? (OracleRef := Unit) maxNodes c with
  | none => false
  | some s =>
    match heapToComb s.nodes s.focus with
    | .error _ => false
    | .ok c' => c == c'

end HeytingLean.CLI.CombFromDAG
