import Lean
import HeytingLean.ProofGraph.Core

namespace HeytingLean.ProofGraph

open Lean

structure FeatureSummary where
  targetDecl : String
  proofSource : String
  infotreeSource : String
  typeNodeReachableCount : Nat
  proofNodeReachableCount : Nat
  typeConstRefs : Array String
  proofConstRefs : Array String
  sharedConstRefs : Array String
  proofOnlyConstRefs : Array String
  typeOnlyConstRefs : Array String
  witnessCount : Nat
  verifierAttached : Bool
  deriving Repr, Inhabited

private def adjacency (edges : Array Edge) : Std.HashMap NodeId (Array NodeId) :=
  edges.foldl
    (fun acc e =>
      let kids := match acc.get? e.src with | some xs => xs | none => #[]
      acc.insert e.src (kids.push e.dst))
    {}

private partial def bfs
    (adj : Std.HashMap NodeId (Array NodeId))
    (queue : List NodeId)
    (seen : Std.HashSet NodeId) : Std.HashSet NodeId :=
  match queue with
  | [] => seen
  | n :: rest =>
      if seen.contains n then
        bfs adj rest seen
      else
        let next := match adj.get? n with | some xs => xs.toList | none => []
        bfs adj (rest ++ next) (seen.insert n)

private def reachableFrom (graph : ProofGraph) (root? : Option NodeId) : Std.HashSet NodeId :=
  let adj := adjacency graph.edges
  match root? with
  | some root => bfs adj [root] {}
  | none => {}

private def collectConstRefs (graph : ProofGraph) (seen : Std.HashSet NodeId) : Std.HashSet String :=
  graph.nodes.foldl
    (fun acc node =>
      if seen.contains node.id then
        match node.exprTag?, node.constName? with
        | some "const_ref", some n => acc.insert n.toString
        | _, _ => acc
      else
        acc)
    {}

private def setToSortedArray (s : Std.HashSet String) : Array String :=
  s.toArray.qsort (fun a b => a < b)

private def inter (a b : Std.HashSet String) : Std.HashSet String :=
  a.fold (init := {}) fun acc x => if b.contains x then acc.insert x else acc

private def diff (a b : Std.HashSet String) : Std.HashSet String :=
  a.fold (init := {}) fun acc x => if b.contains x then acc else acc.insert x

def summarizeFeatures (graph : ProofGraph) : FeatureSummary :=
  let typeReach := reachableFrom graph (some graph.roots.typeRoot)
  let proofReach := reachableFrom graph graph.roots.proofRoot?
  let typeConsts := collectConstRefs graph typeReach
  let proofConsts := collectConstRefs graph proofReach
  let shared := inter typeConsts proofConsts
  let proofOnly := diff proofConsts typeConsts
  let typeOnly := diff typeConsts proofConsts
  { targetDecl := graph.targetDecl.toString
  , proofSource := graph.proofSource.toString
  , infotreeSource := graph.infotreeSource.toString
  , typeNodeReachableCount := typeReach.size
  , proofNodeReachableCount := proofReach.size
  , typeConstRefs := setToSortedArray typeConsts
  , proofConstRefs := setToSortedArray proofConsts
  , sharedConstRefs := setToSortedArray shared
  , proofOnlyConstRefs := setToSortedArray proofOnly
  , typeOnlyConstRefs := setToSortedArray typeOnly
  , witnessCount := graph.witnesses.size
  , verifierAttached := graph.roots.verifierRoot?.isSome
  }

def FeatureSummary.asJson (s : FeatureSummary) : Json :=
  Json.mkObj
    [ ("target_decl", Json.str s.targetDecl)
    , ("proof_source", Json.str s.proofSource)
    , ("infotree_source", Json.str s.infotreeSource)
    , ("type_node_reachable_count", toJson s.typeNodeReachableCount)
    , ("proof_node_reachable_count", toJson s.proofNodeReachableCount)
    , ("type_const_refs", Json.arr <| s.typeConstRefs.map Json.str)
    , ("proof_const_refs", Json.arr <| s.proofConstRefs.map Json.str)
    , ("shared_const_refs", Json.arr <| s.sharedConstRefs.map Json.str)
    , ("proof_only_const_refs", Json.arr <| s.proofOnlyConstRefs.map Json.str)
    , ("type_only_const_refs", Json.arr <| s.typeOnlyConstRefs.map Json.str)
    , ("witness_count", toJson s.witnessCount)
    , ("verifier_attached", Json.bool s.verifierAttached)
    ]

end HeytingLean.ProofGraph
