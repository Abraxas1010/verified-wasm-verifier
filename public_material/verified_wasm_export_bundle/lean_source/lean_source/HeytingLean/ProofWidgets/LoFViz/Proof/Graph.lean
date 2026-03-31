import Lean
import Lean.Data.Json

/-!
# LoF proof graph

The primitive LoF journal encodes only the succession of `mark`/`unmark`/`reentry`
events.  In order to drive richer visualisations we promote that linear log to a
graph that captures both the temporal evolution of the LoF state and the
structural dependencies extracted from the proof term.

This module declares the graph datatypes together with light-weight helpers for
building and inspecting them.  The actual construction from Lean expressions is
implemented in `Proof/Core`.
-/

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz
namespace Proof
namespace Graph

open Lean

/-- Unique identifier for graph nodes. -/
abbrev NodeId := Nat

/-- Classification of nodes in the LoF proof graph. -/
inductive NodeKind
  /-- Snapshot of the LoF state after a primitive has been applied. -/
  | state
  /-- Primitive interaction (`mark`, `unmark`, `reentry`) at a specific journal index. -/
  | primitive
  /-- Proof-term fragment such as a lambda, application, or reference. -/
  | term
  deriving Repr, DecidableEq, Inhabited

namespace NodeKind

def toString : NodeKind → String
  | .state      => "state"
  | .primitive  => "primitive"
  | .term       => "term"

instance : ToString NodeKind := ⟨toString⟩

end NodeKind

/-- Specific primitive actions that appear as nodes. -/
inductive PrimitiveKind
  | mark
  | unmark
  | reentry
  deriving Repr, DecidableEq, Inhabited

namespace PrimitiveKind

def toString : PrimitiveKind → String
  | .mark    => "Mark"
  | .unmark  => "Unmark"
  | .reentry => "Re-entry"

instance : ToString PrimitiveKind := ⟨toString⟩

end PrimitiveKind

/-- Node payload describing LoF and proof-term metadata. -/
structure Node where
  id        : NodeId := 0
  kind      : NodeKind
  depth     : Nat := 0
  label     : String := ""
  region    : Array String := #[]
  journalIx : Option Nat := none
  primitive : Option PrimitiveKind := none
  const?    : Option Name := none
  deriving Repr, Inhabited

/-- Categorisation for edges in the LoF proof graph. -/
inductive EdgeKind
  /-- Successor relation in the LoF journal (`state` → `primitive` → `state`). -/
  | journal
  /-- Dependency generated from the structure of the proof term. -/
  | dependency
  /-- Helper edges used by domain-specific lenses. -/
  | lens
  deriving Repr, DecidableEq, Inhabited

namespace EdgeKind

def toString : EdgeKind → String
  | .journal    => "journal"
  | .dependency => "dependency"
  | .lens       => "lens"

instance : ToString EdgeKind := ⟨toString⟩

end EdgeKind

/-- Edge payload connecting two node identifiers. -/
structure Edge where
  src     : NodeId
  dst     : NodeId
  kind    : EdgeKind
  weight  : Nat := 1
  label   : String := ""
  deriving Repr, Inhabited

/-- Full graph bundle produced for each proof constant. -/
structure ProofGraph where
  nodes    : Array Node := #[]
  edges    : Array Edge := #[]
  root     : Option NodeId := none
  deriving Repr, Inhabited

namespace ProofGraph

/-- Helper for appending a node and returning its identifier. -/
def pushNode (g : ProofGraph) (node : Node) : ProofGraph × NodeId :=
  let id := g.nodes.size
  ({ g with nodes := g.nodes.push { node with id } }, id)

/-- Append an edge to the graph. -/
def pushEdge (g : ProofGraph) (edge : Edge) : ProofGraph :=
  { g with edges := g.edges.push edge }

end ProofGraph

private def jsonOfOption {α} (f : α → Json) : Option α → Json
  | some x => f x
  | none   => Json.null

def Node.toJson (n : Node) : Json :=
  Json.mkObj
    [("id", Json.num n.id),
      ("kind", Json.str n.kind.toString),
      ("depth", Json.num n.depth),
      ("label", Json.str n.label),
      ("region", Json.arr (n.region.map Json.str)),
      ("journalIx", jsonOfOption (fun ix => Json.num ix) n.journalIx),
      ("primitive", jsonOfOption (fun pk => Json.str pk.toString) n.primitive),
      ("const", jsonOfOption (fun nm => Json.str (toString nm)) n.const?)]

def Edge.toJson (e : Edge) : Json :=
  Json.mkObj
    [("src", Json.num e.src),
      ("dst", Json.num e.dst),
      ("kind", Json.str e.kind.toString),
      ("weight", Json.num e.weight),
      ("label", Json.str e.label)]

def ProofGraph.toJson (g : ProofGraph) : Json :=
  Json.mkObj
    [("root", jsonOfOption (fun id => Json.num id) g.root),
      ("nodes", Json.arr (g.nodes.map Node.toJson)),
      ("edges", Json.arr (g.edges.map Edge.toJson))]

end Graph
end Proof
end LoFViz
end ProofWidgets
end HeytingLean
