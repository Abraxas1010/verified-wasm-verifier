import HeytingLean.LeanClef.Bridge.ICCInet
import HeytingLean.LeanClef.PHG.CliffordGrade

/-!
# LeanClef.Export.InetMLIR

Emit ICC terms as Inet MLIR text operations.
Format follows Coll (2025) Inet dialect.

Supports two modes:
- Ungraded: standard ICC agents → Inet MLIR ops
- Graded: ICC agents with Clifford grade annotations → Inet MLIR ops + `grade` attributes
-/

namespace LeanClef.Export

open HeytingLean.LoF.ICC
open HeytingLean.Bridge.INet.ICC
open LeanClef.PHG

/-- Map an ICCAgent kind to its Inet MLIR operation name. -/
def agentToMLIROp : ICCAgent → String
  | .var => "inet.ref"
  | .lam => "inet.construct"
  | .app => "inet.construct"
  | .bridge => "inet.construct"
  | .ann => "inet.construct"
  | .dup => "inet.duplicate"
  | .era => "inet.erase"

/-- Emit a single agent as an MLIR operation. -/
def emitAgent (idx : Nat) (node : ICCNode) : String :=
  let op := agentToMLIROp node.kind
  let payloadStr := match node.payload with
    | some pl => " { payload = " ++ toString pl ++ " }"
    | none => ""
  s!"  %{idx} = {op}(){payloadStr} : !inet.agent"

/-- Emit an ICCNet as Inet MLIR text. -/
def emitICCNet (net : ICCNet) : String :=
  let header := "module {\n  func.func @inet_kernel() {\n"
  let agents := (List.range net.nodes.size).filterMap fun i =>
    match net.nodes[i]? with
    | some (some node) => some (emitAgent i node)
    | _ => none
  let body := String.intercalate "\n" agents
  let footer := "\n  }\n}"
  header ++ body ++ footer

/-- Emit an ICC term as MLIR text by lowering then emitting. -/
def iccToMLIRText (t : Term) : String :=
  emitICCNet (lower t)

-- === Graded MLIR emission ===

/-- Emit a single agent as an MLIR operation with an optional grade attribute.
    Grade annotations come from the PHG pass (external to lowering). -/
def emitGradedAgent (idx : Nat) (node : ICCNode) (grade : Option Nat) : String :=
  let op := agentToMLIROp node.kind
  let payloadStr := match node.payload with
    | some pl => s!", payload = {pl}"
    | none => ""
  let gradeStr := match grade with
    | some g => s!", grade = {g}"
    | none => ""
  let attrStr := match payloadStr ++ gradeStr with
    | "" => ""
    | attrs => s!" \{{attrs.drop 2}}"
  s!"  %{idx} = {op}(){attrStr} : !inet.agent"

/-- A grade map assigns optional grade values to agent indices. -/
abbrev GradeMap := Nat → Option Nat

/-- Emit a graded ICCNet as Inet MLIR text with grade attributes. -/
def emitGradedICCNet (net : ICCNet) (grades : GradeMap) : String :=
  let header := "module {\n  func.func @inet_kernel() {\n"
  let agents := (List.range net.nodes.size).filterMap fun i =>
    match net.nodes[i]? with
    | some (some node) => some (emitGradedAgent i node (grades i))
    | _ => none
  let body := String.intercalate "\n" agents
  let footer := "\n  }\n}"
  header ++ body ++ footer

/-- Emit a graded ICC term as MLIR text. -/
def iccToGradedMLIRText (t : Term) (grades : GradeMap) : String :=
  emitGradedICCNet (lower t) grades

end LeanClef.Export
