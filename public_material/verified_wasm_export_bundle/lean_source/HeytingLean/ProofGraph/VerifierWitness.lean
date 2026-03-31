import Lean
import Lean.Data.Json
import HeytingLean.ProofGraph.Core

namespace HeytingLean.ProofGraph

open Lean
open Lean.Json

structure VerifierAttachment where
  root? : Option NodeId := none
  nodes : Array Node := #[]
  edges : Array Edge := #[]
  witnesses : Array Witness := #[]
  deriving Inhabited

def emptyVerifierAttachment : VerifierAttachment := {}

namespace Internal

private def expectField (j : Json) (name : String) : Except String Json :=
  j.getObjVal? name

private def expectArray (j : Json) (name : String) : Except String (Array Json) := do
  let v ← expectField j name
  v.getArr?

private def expectString (j : Json) (name : String) : Except String String :=
  j.getObjValAs? String name

private def optString (j : Json) (name : String) : Option String :=
  match j.getObjValAs? String name with
  | .ok s => some s
  | .error _ => none

private def optBool (j : Json) (name : String) : Option Bool :=
  match j.getObjValAs? Bool name with
  | .ok b => some b
  | .error _ => none

private def optNat (j : Json) (name : String) : Option Nat :=
  match j.getObjValAs? Nat name with
  | .ok n => some n
  | .error _ => none

private def fileDigestRef (artifactPath : System.FilePath) (declName opType suffix : String) : String :=
  s!"{artifactPath}:{declName}:{opType}:{suffix}"

private def witnessStatusOfRow (status : String) : WitnessStatus :=
  if status = "ok" then .attached else .unavailable

private def appendNode
    (nodes : Array Node)
    (nextId : Nat)
    (kind : NodeKind)
    (label : String)
    (depth : Nat)
    (exprTag? : Option String := none) : Nat × Array Node :=
  let node : Node := { id := nextId, kind, depth, label, exprTag? }
  (nextId + 1, nodes.push node)

private def commandLineage (toolName : String) : Array String :=
  #[toolName, "HeytingLean/CLI/VerifiedCheck.lean"]

end Internal

def attachBenchmarkArtifact (graph : ProofGraph) (artifactPath : System.FilePath) : IO (Except String ProofGraph) := do
  if !(← artifactPath.pathExists) then
    return .error s!"verifier artifact not found: {artifactPath}"
  let raw ← IO.FS.readFile artifactPath
  let json ←
    match Json.parse raw with
    | .ok j => pure j
    | .error e => return .error s!"failed to parse verifier artifact {artifactPath}: {e}"
  match Internal.expectArray json "per_declaration" with
  | .error e => return .error s!"verifier artifact missing per_declaration: {e}"
  | .ok perDecl =>
      let declName := graph.targetDecl.toString
      match perDecl.find? (fun j =>
          match j.getObjValAs? String "decl_name" with
          | .ok s => s = declName
          | .error _ => false) with
      | none => return .ok graph
      | some declRow =>
          match Internal.expectArray declRow "rows" with
          | .error e => return .error s!"verifier artifact row missing rows for {declName}: {e}"
          | .ok rows =>
              let toolName := Internal.optString json "tool" |>.getD "verifier_artifact"
              let mut nextId := graph.nodes.size
              let mut newNodes := graph.nodes
              let mut newEdges := graph.edges
              let mut newWitnesses := graph.witnesses
              let (nextId', newNodes') := Internal.appendNode newNodes nextId .verifierObligation
                s!"verifier {artifactPath.fileName.getD artifactPath.toString}" 0 (some "verifier_root")
              nextId := nextId'
              newNodes := newNodes'
              let rootId := nextId - 1
              match graph.nodes[0]? with
              | some declRoot =>
                  newEdges := newEdges.push { src := declRoot.id, dst := rootId, kind := .verifiedBy, label := "artifact" }
              | none => pure ()
              for row in rows do
                let opType := Internal.optString row "op_type" |>.getD "unknown"
                let status := Internal.optString row "status" |>.getD "unknown"
                let payloadWritten := Internal.optBool row "payload_written" |>.getD false
                let skyWritten := Internal.optBool row "sky_written" |>.getD false
                let obligationsTotal :=
                  match row.getObjVal? "sky_summary" with
                  | .ok sky => Internal.optNat sky "obligations_total"
                  | .error _ => none
                let opLabel :=
                  match obligationsTotal with
                  | some n => s!"{opType}:{status}:{n} obligations"
                  | none => s!"{opType}:{status}"
                let (nextId'', newNodes'') := Internal.appendNode newNodes nextId .verifierObligation
                  opLabel 1 (some "verifier_op")
                nextId := nextId''
                newNodes := newNodes''
                let opNodeId := nextId - 1
                newEdges := newEdges.push { src := rootId, dst := opNodeId, kind := .verifiedBy, label := opType }
                if payloadWritten then
                  newWitnesses := newWitnesses.push
                    { kind := .verifiedCheck
                    , status := Internal.witnessStatusOfRow status
                    , digestOrArtifact := Internal.fileDigestRef artifactPath declName opType "payload"
                    , commandLineage := Internal.commandLineage toolName
                    , node? := some opNodeId
                    }
                if skyWritten then
                  newWitnesses := newWitnesses.push
                    { kind := .skyV1
                    , status := Internal.witnessStatusOfRow status
                    , digestOrArtifact := Internal.fileDigestRef artifactPath declName opType "sky"
                    , commandLineage := Internal.commandLineage toolName
                    , node? := some opNodeId
                    }
              let updated : ProofGraph :=
                { graph with
                    roots := { graph.roots with verifierRoot? := some rootId }
                    nodes := newNodes
                    edges := newEdges
                    witnesses := newWitnesses
                }
              return .ok (withFreshMetrics updated)

end HeytingLean.ProofGraph
