import Lean
import Lean.Data.Json

namespace HeytingLean.ProofGraph

open Lean

abbrev NodeId := Nat

inductive ProofSource
  | kernelValue
  | erased
  | infotreeReconstructed
  | unavailable
  deriving Repr, DecidableEq, Inhabited

namespace ProofSource

def toString : ProofSource → String
  | .kernelValue => "kernel_value"
  | .erased => "erased"
  | .infotreeReconstructed => "infotree_reconstructed"
  | .unavailable => "unavailable"

instance : ToString ProofSource := ⟨toString⟩

end ProofSource

inductive InfoTreeSource
  | attached
  | offlineUnavailable
  | unavailable
  deriving Repr, DecidableEq, Inhabited

namespace InfoTreeSource

def toString : InfoTreeSource → String
  | .attached => "attached"
  | .offlineUnavailable => "offline_unavailable"
  | .unavailable => "unavailable"

instance : ToString InfoTreeSource := ⟨toString⟩

end InfoTreeSource

inductive NodeKind
  | decl
  | typeExpr
  | proofExpr
  | binder
  | const
  | app
  | forallE
  | lam
  | letE
  | sort
  | lit
  | proj
  | bvar
  | fvar
  | mvar
  | mdata
  | unknown
  | infotreeTerm
  | infotreeTactic
  | verifierObligation
  | externalCheckerWitness
  deriving Repr, DecidableEq, Inhabited

namespace NodeKind

def toString : NodeKind → String
  | .decl => "decl"
  | .typeExpr => "type_expr"
  | .proofExpr => "proof_expr"
  | .binder => "binder"
  | .const => "const"
  | .app => "app"
  | .forallE => "forall"
  | .lam => "lam"
  | .letE => "let"
  | .sort => "sort"
  | .lit => "lit"
  | .proj => "proj"
  | .bvar => "bvar"
  | .fvar => "fvar"
  | .mvar => "mvar"
  | .mdata => "mdata"
  | .unknown => "unknown"
  | .infotreeTerm => "infotree_term"
  | .infotreeTactic => "infotree_tactic"
  | .verifierObligation => "verifier_obligation"
  | .externalCheckerWitness => "external_checker_witness"

instance : ToString NodeKind := ⟨toString⟩

end NodeKind

inductive EdgeKind
  | exprChild
  | typeOf
  | proves
  | usesConst
  | elaboratesTo
  | verifiedBy
  | replaysTo
  | dependsOn
  | infotreeParent
  deriving Repr, DecidableEq, Inhabited

namespace EdgeKind

def toString : EdgeKind → String
  | .exprChild => "expr_child"
  | .typeOf => "type_of"
  | .proves => "proves"
  | .usesConst => "uses_const"
  | .elaboratesTo => "elaborates_to"
  | .verifiedBy => "verified_by"
  | .replaysTo => "replays_to"
  | .dependsOn => "depends_on"
  | .infotreeParent => "infotree_parent"

instance : ToString EdgeKind := ⟨toString⟩

end EdgeKind

inductive WitnessKind
  | verifiedCheck
  | skyV1
  | lean4lean
  | kernelOnly
  deriving Repr, DecidableEq, Inhabited

namespace WitnessKind

def toString : WitnessKind → String
  | .verifiedCheck => "verified_check"
  | .skyV1 => "sky_v1"
  | .lean4lean => "lean4lean"
  | .kernelOnly => "kernel_only"

instance : ToString WitnessKind := ⟨toString⟩

end WitnessKind

inductive WitnessStatus
  | attached
  | unavailable
  deriving Repr, DecidableEq, Inhabited

namespace WitnessStatus

def toString : WitnessStatus → String
  | .attached => "attached"
  | .unavailable => "unavailable"

instance : ToString WitnessStatus := ⟨toString⟩

end WitnessStatus

structure Roots where
  typeRoot : NodeId
  proofRoot? : Option NodeId := none
  infotreeRoot? : Option NodeId := none
  verifierRoot? : Option NodeId := none
  deriving Repr, Inhabited

structure Node where
  id : NodeId
  kind : NodeKind
  depth : Nat := 0
  label : String := ""
  constName? : Option Name := none
  exprTag? : Option String := none
  deriving Repr, Inhabited

structure Edge where
  src : NodeId
  dst : NodeId
  kind : EdgeKind
  label : String := ""
  deriving Repr, Inhabited

structure Witness where
  kind : WitnessKind
  status : WitnessStatus
  digestOrArtifact : String
  commandLineage : Array String := #[]
  node? : Option NodeId := none
  deriving Repr, Inhabited

structure GraphMetrics where
  nodeCount : Nat := 0
  edgeCount : Nat := 0
  hyperedgeCount : Nat := 0
  witnessCount : Nat := 0
  sharedExprNodes : Nat := 0
  deriving Repr, Inhabited

structure ProofGraph where
  schema : String := "HeytingLean/ProofGraph/v1"
  targetDecl : Name
  moduleName : Name
  declKind : String
  proofSource : ProofSource
  infotreeSource : InfoTreeSource := .unavailable
  roots : Roots
  nodes : Array Node := #[]
  edges : Array Edge := #[]
  hyperedges : Array (Array NodeId) := #[]
  witnesses : Array Witness := #[]
  metrics : GraphMetrics := {}
  deriving Repr, Inhabited

private def jNat (n : Nat) : Json :=
  Json.num (JsonNumber.fromNat n)

private def jsonOfOption {α} (f : α → Json) : Option α → Json
  | some x => f x
  | none => Json.null

def Roots.asJson (r : Roots) : Json :=
  Json.mkObj
    [ ("type_root", jNat r.typeRoot)
    , ("proof_root", jsonOfOption jNat r.proofRoot?)
    , ("infotree_root", jsonOfOption jNat r.infotreeRoot?)
    , ("verifier_root", jsonOfOption jNat r.verifierRoot?)
    ]

def Node.asJson (n : Node) : Json :=
  Json.mkObj
    [ ("id", jNat n.id)
    , ("kind", Json.str n.kind.toString)
    , ("depth", jNat n.depth)
    , ("label", Json.str n.label)
    , ("const_name", jsonOfOption (Json.str ∘ Name.toString) n.constName?)
    , ("expr_tag", jsonOfOption Json.str n.exprTag?)
    ]

def Edge.asJson (e : Edge) : Json :=
  Json.mkObj
    [ ("src", jNat e.src)
    , ("dst", jNat e.dst)
    , ("kind", Json.str e.kind.toString)
    , ("label", Json.str e.label)
    ]

def Witness.asJson (w : Witness) : Json :=
  Json.mkObj
    [ ("kind", Json.str w.kind.toString)
    , ("status", Json.str w.status.toString)
    , ("digest_or_artifact", Json.str w.digestOrArtifact)
    , ("command_lineage", Json.arr <| w.commandLineage.map Json.str)
    , ("node", jsonOfOption jNat w.node?)
    ]

def GraphMetrics.asJson (m : GraphMetrics) : Json :=
  Json.mkObj
    [ ("node_count", jNat m.nodeCount)
    , ("edge_count", jNat m.edgeCount)
    , ("hyperedge_count", jNat m.hyperedgeCount)
    , ("witness_count", jNat m.witnessCount)
    , ("shared_expr_nodes", jNat m.sharedExprNodes)
    ]

def ProofGraph.asJson (g : ProofGraph) : Json :=
  Json.mkObj
    [ ("schema", Json.str g.schema)
    , ("target_decl", Json.str g.targetDecl.toString)
    , ("module", Json.str g.moduleName.toString)
    , ("decl_kind", Json.str g.declKind)
    , ("proof_source", Json.str g.proofSource.toString)
    , ("infotree_source", Json.str g.infotreeSource.toString)
    , ("roots", g.roots.asJson)
    , ("nodes", Json.arr <| g.nodes.map Node.asJson)
    , ("edges", Json.arr <| g.edges.map Edge.asJson)
    , ("hyperedges", Json.arr <| g.hyperedges.map (fun hs => Json.arr <| hs.map jNat))
    , ("witnesses", Json.arr <| g.witnesses.map Witness.asJson)
    , ("metrics", g.metrics.asJson)
    ]

def moduleOfDecl (declName : Name) : Name :=
  declName.getPrefix

def withFreshMetrics (g : ProofGraph) : ProofGraph :=
  { g with metrics :=
      { nodeCount := g.nodes.size
      , edgeCount := g.edges.size
      , hyperedgeCount := g.hyperedges.size
      , witnessCount := g.witnesses.size
      , sharedExprNodes := g.metrics.sharedExprNodes
      } }

end HeytingLean.ProofGraph
