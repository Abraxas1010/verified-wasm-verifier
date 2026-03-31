import Lean
import HeytingLean.ProofGraph.Core

namespace HeytingLean.ProofGraph

open Lean

structure ExtractState where
  nextId : Nat := 0
  nodes : Array Node := #[]
  edges : Array Edge := #[]
  memo : Std.HashMap Expr NodeId := {}
  sharedExprNodes : Nat := 0
  deriving Inhabited

abbrev ExtractM := StateM ExtractState

private def pushNode (kind : NodeKind) (label : String) (depth : Nat)
    (constName? : Option Name := none) (exprTag? : Option String := none) : ExtractM NodeId := do
  let st ← get
  let id := st.nextId
  let node : Node := { id, kind, depth, label, constName?, exprTag? }
  set { st with nextId := id + 1, nodes := st.nodes.push node }
  return id

private def pushEdge (src dst : NodeId) (kind : EdgeKind) (label : String := "") : ExtractM Unit := do
  modify fun st => { st with edges := st.edges.push { src, dst, kind, label } }

private def exprKind : Expr → NodeKind
  | .forallE .. => .forallE
  | .lam .. => .lam
  | .app .. => .app
  | .const .. => .const
  | .sort .. => .sort
  | .letE .. => .letE
  | .lit .. => .lit
  | .proj .. => .proj
  | .bvar .. => .bvar
  | .fvar .. => .fvar
  | .mvar .. => .mvar
  | .mdata .. => .mdata

private def exprLabel : Expr → String
  | .forallE n _ _ _ => s!"∀ {n}"
  | .lam n _ _ _ => s!"λ {n}"
  | .const n _ => n.toString
  | .sort u => s!"Sort {u}"
  | .letE n _ _ _ _ => s!"let {n}"
  | .lit (.natVal n) => s!"nat {n}"
  | .lit (.strVal s) => s!"str \"{s}\""
  | .proj n i _ => s!"proj {n}:{i}"
  | .bvar idx => s!"bvar {idx}"
  | .fvar fid => s!"fvar {fid.name}"
  | .mvar mid => s!"mvar {mid.name}"
  | .mdata .. => "mdata"
  | .app .. => "app"

private def exprConstName? : Expr → Option Name
  | .const n _ => some n
  | _ => none

partial def addExpr (e : Expr) (depth fuel : Nat) : ExtractM NodeId := do
  if fuel == 0 then
    return ← pushNode .unknown "… (fuel exhausted)" depth none (some "fuel_exhausted")
  match (← get).memo.get? e with
  | some id =>
      modify fun st => { st with sharedExprNodes := st.sharedExprNodes + 1 }
      return id
  | none =>
      let id ← pushNode (exprKind e) (exprLabel e) depth (exprConstName? e) none
      modify fun st => { st with memo := st.memo.insert e id }
      let attach (child : Expr) (edgeKind : EdgeKind := .exprChild) (label : String := "") : ExtractM Unit := do
        let cid ← addExpr child (depth + 1) (fuel - 1)
        pushEdge id cid edgeKind label
      match e with
      | .forallE n ty body _ => do
          let binder ← pushNode .binder n.toString (depth + 1) none (some "forall_binder")
          pushEdge id binder .exprChild "binder"
          attach ty .exprChild "ty"
          attach body .exprChild "body"
      | .lam n ty body _ => do
          let binder ← pushNode .binder n.toString (depth + 1) none (some "lam_binder")
          pushEdge id binder .exprChild "binder"
          attach ty .exprChild "ty"
          attach body .exprChild "body"
      | .app f a => do
          attach f .exprChild "fn"
          attach a .exprChild "arg"
      | .letE n ty val body _ => do
          let binder ← pushNode .binder n.toString (depth + 1) none (some "let_binder")
          pushEdge id binder .exprChild "binder"
          attach ty .exprChild "ty"
          attach val .exprChild "val"
          attach body .exprChild "body"
      | .mdata _ body => do
          attach body .exprChild "body"
      | .proj _ _ body => do
          attach body .exprChild "struct"
      | .const n _ => do
          let dep ← pushNode .decl n.toString (depth + 1) (some n) (some "const_ref")
          pushEdge id dep .usesConst ""
      | _ => pure ()
      return id

private def addRoot (kind : NodeKind) (label : String) (body : Expr) (fuel : Nat) : ExtractM NodeId := do
  let root ← pushNode kind label 0 none none
  let bodyId ← addExpr body 1 fuel
  pushEdge root bodyId .exprChild "body"
  return root

structure ExtractedRoots where
  declRoot : NodeId
  typeRoot : NodeId
  proofRoot? : Option NodeId := none
  nodes : Array Node
  edges : Array Edge
  sharedExprNodes : Nat
  deriving Inhabited

def extractDeclGraph (declName : Name) (typeExpr : Expr) (proofExpr? : Option Expr := none)
    (fuel : Nat := 4096) : ExtractedRoots :=
  let init : ExtractState := {}
  let ((declRoot, typeRoot, proofRoot?), st) := Id.run <| (do
    let declRoot ← pushNode .decl declName.toString 0 (some declName) (some "decl")
    let typeRoot ← addRoot .typeExpr "type" typeExpr fuel
    pushEdge declRoot typeRoot .typeOf "type"
    let proofRoot? ← match proofExpr? with
      | some proofExpr =>
          let proofRoot ← addRoot .proofExpr "proof" proofExpr fuel
          pushEdge declRoot proofRoot .proves "proof"
          pure (some proofRoot)
      | none => pure none
    return (declRoot, typeRoot, proofRoot?)).run init
  { declRoot, typeRoot, proofRoot?, nodes := st.nodes, edges := st.edges, sharedExprNodes := st.sharedExprNodes }

end HeytingLean.ProofGraph
