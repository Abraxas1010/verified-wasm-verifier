import HeytingLean.LoF.Combinators.SKY

/-!
# Bridge.INet.Basic

Minimal Level 3 interaction-net data structures for direct SKY encoding.
This file defines the agent vocabulary, ports, lightweight net container,
and active-pair detection. It is intentionally small enough to support
later soundness work without committing to the full runtime algorithm yet.
-/

namespace HeytingLean.Bridge.INet

open HeytingLean.LoF

/-- Agent vocabulary for the staged direct SKY interaction-net bridge. -/
inductive SKYAgent where
  | app
  | s
  | s1
  | s2
  | k
  | k1
  | y
  | dup
  | era
  deriving DecidableEq, Repr, Inhabited

/-- Physical auxiliary-port count for each agent. -/
def SKYAgent.arity : SKYAgent → Nat
  | .app => 2
  | .s => 0
  | .s1 => 1
  | .s2 => 2
  | .k => 0
  | .k1 => 1
  | .y => 0
  | .dup => 2
  | .era => 0

def SKYAgent.isLeaf : SKYAgent → Bool
  | .s | .k | .y | .era => true
  | _ => false

inductive PortRole where
  | principal
  | aux1
  | aux2
  deriving DecidableEq, Repr, Inhabited, BEq

def PortRole.toNat : PortRole → Nat
  | .principal => 0
  | .aux1 => 1
  | .aux2 => 2

instance : Hashable PortRole where
  hash := hash ∘ PortRole.toNat

/-- A concrete port inside an interaction net. -/
structure Port where
  agent : Nat
  role : PortRole
  deriving DecidableEq, Repr, Inhabited, BEq

instance : Hashable Port where
  hash p := mixHash (hash p.agent) (hash p.role)

def Port.isPrincipal (p : Port) : Bool :=
  p.role = .principal

/-- Runtime node metadata.

`captures` tracks staged environment information for partial applications.
It is separate from the physical auxiliary-port shape so the Level 3 model
can represent lazy `Y` closures without inventing extra agent kinds. -/
structure AgentNode where
  kind : SKYAgent
  captures : Array Port := #[]
  deriving Repr, Inhabited

def AgentNode.auxPortCount (node : AgentNode) : Nat :=
  node.kind.arity

def AgentNode.wellFormed (node : AgentNode) : Prop :=
  node.captures.size ≤ 2

/-- Symmetric wire between two concrete ports. -/
structure Wire where
  lhs : Port
  rhs : Port
  deriving DecidableEq, Repr, Inhabited

def Wire.involves (w : Wire) (p : Port) : Bool :=
  w.lhs == p || w.rhs == p

def Wire.other? (w : Wire) (p : Port) : Option Port :=
  if w.lhs == p then
    some w.rhs
  else if w.rhs == p then
    some w.lhs
  else
    none

/-- Lightweight interaction-net container used by the direct SKY bridge. -/
structure INet where
  agents : Array (Option AgentNode)
  wires : List Wire
  root : Port
  deriving Repr, Inhabited

def INet.empty : INet :=
  { agents := #[], wires := [], root := ⟨0, .principal⟩ }

def INet.singleton (kind : SKYAgent) : INet :=
  { agents := #[some { kind := kind }]
    wires := []
    root := ⟨0, .principal⟩ }

def Port.shiftAgent (p : Port) (delta : Nat) : Port :=
  { p with agent := p.agent + delta }

def Wire.shiftAgent (w : Wire) (delta : Nat) : Wire :=
  { lhs := w.lhs.shiftAgent delta, rhs := w.rhs.shiftAgent delta }

def INet.node? (net : INet) (agent : Nat) : Option AgentNode :=
  match net.agents[agent]? with
  | some node? => node?
  | none => none

def INet.kind? (net : INet) (agent : Nat) : Option SKYAgent := do
  let node <- net.node? agent
  pure node.kind

def INet.appendAgent (net : INet) (node : AgentNode) : INet × Nat :=
  let idx := net.agents.size
  ({ net with agents := net.agents.push (some node) }, idx)

def INet.eraseAgent (net : INet) (agent : Nat) : INet :=
  if _h : agent < net.agents.size then
    { net with agents := net.agents.set! agent none }
  else
    net

def INet.connect (net : INet) (lhs rhs : Port) : INet :=
  { net with wires := { lhs := lhs, rhs := rhs } :: net.wires }

def INet.connectedTo? (net : INet) (port : Port) : Option Port :=
  net.wires.findSome? (fun wire => wire.other? port)

def INet.validPort (net : INet) (port : Port) : Prop :=
  match net.kind? port.agent with
  | none => False
  | some kind => port.role.toNat ≤ kind.arity

/-- Principal-to-principal active pairs. -/
def INet.activePairs (net : INet) : List (Nat × Nat) :=
  net.wires.foldr
    (fun wire acc =>
      if wire.lhs.isPrincipal && wire.rhs.isPrincipal then
        (wire.lhs.agent, wire.rhs.agent) :: acc
      else
        acc)
    []

def INet.isNormalForm (net : INet) : Prop :=
  net.activePairs = []

def INet.agentCount (net : INet) : Nat :=
  net.agents.foldl (fun acc node? => if node?.isSome then acc + 1 else acc) 0

/-- Direct structural encoding into a trivial tree-shaped net.
This mirrors the 4-arm compiler surface and is sufficient for Phase 1 scaffolding. -/
def encodeComb : LoF.Comb → INet
  | .S => INet.singleton .s
  | .K => INet.singleton .k
  | .Y => INet.singleton .y
  | .app f x =>
      let fNet := encodeComb f
      let xNet := encodeComb x
      let xShift := fNet.agents.size
      let xRoot := xNet.root.shiftAgent xShift
      let xWires := xNet.wires.map (·.shiftAgent xShift)
      let baseAgents := fNet.agents ++ xNet.agents
      let rootIdx := baseAgents.size
      let appNode : AgentNode := { kind := .app }
      { agents := baseAgents.push (some appNode)
        wires :=
          fNet.wires ++
          xWires ++
          [ { lhs := ⟨rootIdx, .aux1⟩, rhs := fNet.root }
          , { lhs := ⟨rootIdx, .aux2⟩, rhs := xRoot }
          ]
        root := ⟨rootIdx, .principal⟩ }

example : SKYAgent.arity .s2 = 2 := rfl
example : SKYAgent.arity .k1 = 1 := rfl
example : (INet.singleton .s).activePairs = [] := rfl

end HeytingLean.Bridge.INet
