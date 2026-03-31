import HeytingLean.LoF.ICC.Syntax

namespace HeytingLean.Bridge.INet.ICC

open HeytingLean.LoF.ICC

/--
Parallel ICC agent vocabulary for the additive lane.

Unlike the current production `SKYAgent`, this vocabulary includes an explicit
`var` leaf because the audited public ICC syntax includes `Var`.
-/
inductive ICCAgent where
  | var
  | lam
  | app
  | bridge
  | ann
  | dup
  | era
  deriving DecidableEq, Repr, Inhabited

def ICCAgent.arity : ICCAgent → Nat
  | .var => 0
  | .lam => 1
  | .app => 2
  | .bridge => 1
  | .ann => 2
  | .dup => 2
  | .era => 0

inductive PortRole where
  | principal
  | aux1
  | aux2
  deriving DecidableEq, Repr, Inhabited, BEq

inductive RewriteClass where
  | appLam
  | appBridge
  | annLam
  | annBridge
  | unsupported
  | none
  deriving DecidableEq, Repr, Inhabited, BEq

def RewriteClass.toString : RewriteClass → String
  | .appLam => "app_lam"
  | .appBridge => "app_bridge"
  | .annLam => "ann_lam"
  | .annBridge => "ann_bridge"
  | .unsupported => "unsupported"
  | .none => "none"

def PortRole.toNat : PortRole → Nat
  | .principal => 0
  | .aux1 => 1
  | .aux2 => 2

instance : Hashable PortRole where
  hash := hash ∘ PortRole.toNat

structure Port where
  agent : Nat
  role : PortRole
  deriving DecidableEq, Repr, Inhabited, BEq

instance : Hashable Port where
  hash p := mixHash (hash p.agent) (hash p.role)

def Port.isPrincipal (p : Port) : Bool :=
  p.role = .principal

structure Wire where
  lhs : Port
  rhs : Port
  deriving DecidableEq, Repr, Inhabited

def Wire.other? (w : Wire) (p : Port) : Option Port :=
  if w.lhs == p then
    some w.rhs
  else if w.rhs == p then
    some w.lhs
  else
    none

structure ICCNode where
  kind : ICCAgent
  captures : Array Port := #[]
  payload : Option Nat := none
  deriving Repr, Inhabited

structure ICCNet where
  nodes : Array (Option ICCNode)
  wires : List Wire
  root : Port
  deriving Repr, Inhabited

def ICCNet.empty : ICCNet :=
  { nodes := #[], wires := [], root := ⟨0, .principal⟩ }

def ICCNet.singleton (kind : ICCAgent) : ICCNet :=
  { nodes := #[some { kind := kind }]
    wires := []
    root := ⟨0, .principal⟩ }

def Port.shiftAgent (p : Port) (delta : Nat) : Port :=
  { p with agent := p.agent + delta }

def Wire.shiftAgent (w : Wire) (delta : Nat) : Wire :=
  { lhs := w.lhs.shiftAgent delta, rhs := w.rhs.shiftAgent delta }

def ICCNet.node? (net : ICCNet) (agent : Nat) : Option ICCNode :=
  match net.nodes[agent]? with
  | some node? => node?
  | none => none

def ICCNet.connect (net : ICCNet) (lhs rhs : Port) : ICCNet :=
  { net with wires := { lhs := lhs, rhs := rhs } :: net.wires }

def ICCNet.connectedTo? (net : ICCNet) (port : Port) : Option Port :=
  net.wires.findSome? (fun wire => wire.other? port)

def ICCNet.rewritePairOnWire? (net : ICCNet) (wire : Wire) : Option (Nat × Nat) := do
  let lhsNode ← net.node? wire.lhs.agent
  let rhsNode ← net.node? wire.rhs.agent
  let mk := (wire.lhs.agent, wire.rhs.agent)
  let mkSwap := (wire.rhs.agent, wire.lhs.agent)
  if lhsNode.kind = .app && wire.lhs.role = .aux1 &&
      wire.rhs.role = .principal &&
      (rhsNode.kind = .lam || rhsNode.kind = .bridge) then
    some mk
  else if rhsNode.kind = .app && wire.rhs.role = .aux1 &&
      wire.lhs.role = .principal &&
      (lhsNode.kind = .lam || lhsNode.kind = .bridge) then
    some mkSwap
  else if lhsNode.kind = .ann && wire.lhs.role = .aux2 &&
      wire.rhs.role = .principal &&
      (rhsNode.kind = .lam || rhsNode.kind = .bridge) then
    some mk
  else if rhsNode.kind = .ann && wire.rhs.role = .aux2 &&
      wire.lhs.role = .principal &&
      (lhsNode.kind = .lam || lhsNode.kind = .bridge) then
    some mkSwap
  else
    none

def ICCNet.classifyWireCore (net : ICCNet) (wire : Wire) : RewriteClass := Id.run do
  let some lhsNode := net.node? wire.lhs.agent | return .none
  let some rhsNode := net.node? wire.rhs.agent | return .none
  let appLamLike (kind : ICCAgent) : Option RewriteClass :=
    match kind with
    | .lam => some .appLam
    | .bridge => some .appBridge
    | _ => none
  let annLamLike (kind : ICCAgent) : Option RewriteClass :=
    match kind with
    | .lam => some .annLam
    | .bridge => some .annBridge
    | _ => none
  if lhsNode.kind = .app && wire.lhs.role = .aux1 && wire.rhs.role = .principal then
    match appLamLike rhsNode.kind with
    | some cls => cls
    | none => .unsupported
  else if rhsNode.kind = .app && wire.rhs.role = .aux1 && wire.lhs.role = .principal then
    match appLamLike lhsNode.kind with
    | some cls => cls
    | none => .unsupported
  else if lhsNode.kind = .ann && wire.lhs.role = .aux2 && wire.rhs.role = .principal then
    match annLamLike rhsNode.kind with
    | some cls => cls
    | none => .unsupported
  else if rhsNode.kind = .ann && wire.rhs.role = .aux2 && wire.lhs.role = .principal then
    match annLamLike lhsNode.kind with
    | some cls => cls
    | none => .unsupported
  else
    .none

def ICCNet.activePairs (net : ICCNet) : List (Nat × Nat) :=
  net.wires.filterMap (net.rewritePairOnWire? ·)

def ICCNet.classifyWire (net : ICCNet) (wire : Wire) : RewriteClass :=
  net.classifyWireCore wire

def ICCNet.activePairClasses (net : ICCNet) : List RewriteClass :=
  net.wires.foldr
    (fun wire acc =>
      match net.classifyWire wire with
      | .none => acc
      | cls => cls :: acc)
    []

def ICCNet.agentCount (net : ICCNet) : Nat :=
  net.nodes.foldl (fun acc node? => if node?.isSome then acc + 1 else acc) 0

def ICCNet.isNormalForm (net : ICCNet) : Prop :=
  net.activePairs = []

end HeytingLean.Bridge.INet.ICC
