import HeytingLean.Embeddings.Adelic

/-!
# ATP.ProofNetwork

Minimal proof-network scaffolding for lane-changing ATP.

This is a small, executable data structure:
- nodes are labeled by a `LensID` and an optional string label,
- edges record “transport/gluing” relationships between nodes.

It is intentionally *not* a full proof-state graph of the Lean kernel; it is a bookkeeping layer
that can be fed by future proof-search tooling.
-/

namespace HeytingLean
namespace ATP

open HeytingLean.Embeddings

/-- Minimal metadata to describe an attempted proof transfer route. -/
structure LensTransfer where
  source : LensID
  target : LensID
  reason : String := ""
  witnessTheorem : String := ""
  deriving Repr

/-- Certificate payload for a blocked/autonomously rejected proof goal. -/
structure BlockedCertificate where
  obstructionClass : String
  cohomologyDegree : Nat := 0
  severity : String := "high"
  recommendedAction : String := ""
  suggestedLenses : List LensID := []
  obligations : List String := []
  theoremWitness : Option String := none
  projectionHints : List String := []
  notes : List String := []
  deriving Repr

/-- Certificate payload for an accepted proof route. -/
structure ProofArtifact where
  theoremName : String := ""
  theoremStatement : Option String := none
  theoremDecl : Option String := none
  replayScript : Option String := none
  sheafWitnesses : List String := []
  transportTrace : List LensTransfer := []
  cabDigest : Option String := none
  replayLog : List String := []
  deriving Repr

inductive ATPOutcome where
  | inProgress
  | proved (artifact : ProofArtifact)
  | blockedCertified (obligation : BlockedCertificate)
  | failed (msg : String := "")
  deriving Repr

def ATPOutcome.isProved : ATPOutcome → Bool
  | .proved _ => true
  | _ => false

def ATPOutcome.isBlocked : ATPOutcome → Bool
  | .blockedCertified _ => true
  | _ => false

def ATPOutcome.isOpen : ATPOutcome → Bool
  | .inProgress => true
  | _ => false

def ATPOutcome.toString : ATPOutcome → String
  | inProgress => "in_progress"
  | proved _ => "proved"
  | blockedCertified _ => "blocked_certified"
  | failed _ => "failed"

def proofArtifact (name : String) : ProofArtifact where
  theoremName := name

def blocked (className : String) (lensHints : List LensID := []) : ATPOutcome :=
  ATPOutcome.blockedCertified {
    obstructionClass := className,
    suggestedLenses := lensHints
  }

structure ProofNode where
  id : Nat
  lens : LensID
  label : String := ""
  goal : Option String := none
  outcome : ATPOutcome := .inProgress
  deriving Repr

structure ProofEdge where
  src : Nat
  dst : Nat
  label : String := ""
  witness : Option String := none
  deriving Repr

structure ProofNetwork where
  next : Nat := 0
  nodes : Array ProofNode := #[]
  edges : Array ProofEdge := #[]
  deriving Repr

namespace ProofNetwork

def nodeCount (G : ProofNetwork) : Nat := G.nodes.size
def edgeCount (G : ProofNetwork) : Nat := G.edges.size

def findNode (G : ProofNetwork) (id : Nat) : Option ProofNode :=
  G.nodes.find? (fun n => n.id == id)

def setNodeOutcome (G : ProofNetwork) (id : Nat) (o : ATPOutcome) : ProofNetwork :=
  let nodes' :=
    G.nodes.foldl (init := ({} : Array ProofNode)) (fun acc n =>
      if n.id == id then
        acc.push { n with outcome := o }
      else
        acc.push n)
  { G with nodes := nodes' }

def setNodeGoal (G : ProofNetwork) (id : Nat) (g : Option String) : ProofNetwork :=
  let nodes' :=
    G.nodes.foldl (init := ({} : Array ProofNode)) (fun acc n =>
      if n.id == id then
        acc.push { n with goal := g }
      else
        acc.push n)
  { G with nodes := nodes' }

def setNodeLabel (G : ProofNetwork) (id : Nat) (lbl : String) : ProofNetwork :=
  let nodes' :=
    G.nodes.foldl (init := ({} : Array ProofNode)) (fun acc n =>
      if n.id == id then
        acc.push { n with label := lbl }
      else
        acc.push n)
  { G with nodes := nodes' }

def setNodeTransferTrace (G : ProofNetwork) (id : Nat) (trace : List LensTransfer) : ProofNetwork :=
  let nodes' :=
    G.nodes.foldl (init := ({} : Array ProofNode)) (fun acc n =>
      if n.id == id then
        match n.outcome with
        | .proved a => acc.push { n with outcome := .proved { a with transportTrace := trace } }
        | _ => acc.push n
      else
        acc.push n)
  { G with nodes := nodes' }

def setNodeSheafWitnesses (G : ProofNetwork) (id : Nat) (w : List String) : ProofNetwork :=
  let nodes' :=
    G.nodes.foldl (init := ({} : Array ProofNode)) (fun acc n =>
      if n.id == id then
        match n.outcome with
        | .proved a => acc.push { n with outcome := .proved { a with sheafWitnesses := w } }
        | _ => acc.push n
      else
        acc.push n)
  { G with nodes := nodes' }

def addNode (G : ProofNetwork) (lens : LensID) (label : String := "") : ProofNetwork × Nat :=
  let id := G.next
  let node : ProofNode := { id := id, lens := lens, label := label }
  ({ G with next := id + 1, nodes := G.nodes.push node }, id)

def addEdge (G : ProofNetwork) (src dst : Nat) (label : String := "") : ProofNetwork :=
  { G with edges := G.edges.push { src := src, dst := dst, label := label } }

def addWitnessedEdge (G : ProofNetwork) (src dst : Nat) (label witness : String) : ProofNetwork :=
  { G with edges := G.edges.push { src := src, dst := dst, label := label, witness := some witness } }

/-- Number of possible directed edges on `n` labeled nodes, excluding self-loops. -/
def possibleDirectedEdges (n : Nat) : Nat :=
  n * (n - 1)

/-- A tiny “phase transition” heuristic: edge count exceeds node count. -/
def phaseTransitionHeuristic (G : ProofNetwork) : Bool :=
  G.edgeCount ≥ G.nodeCount

end ProofNetwork

end ATP
end HeytingLean
