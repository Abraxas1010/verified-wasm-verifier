import Lean.Data.Json
import HeytingLean.Bridge.INet.ICCBasic

namespace HeytingLean.Bridge.INet.ICC

open Lean
open HeytingLean.LoF.ICC

def shiftNode (node : ICCNode) (delta : Nat) : ICCNode :=
  { node with captures := node.captures.map (·.shiftAgent delta) }

def lower : HeytingLean.LoF.ICC.Term → ICCNet
  | .var idx =>
      { nodes := #[some { kind := .var, payload := some idx }]
        wires := []
        root := ⟨0, .principal⟩ }
  | .lam body =>
      let bodyNet := lower body
      let rootIdx := bodyNet.nodes.size
      { nodes := bodyNet.nodes.push (some { kind := .lam, captures := #[bodyNet.root] })
        wires := bodyNet.wires ++ [{ lhs := ⟨rootIdx, .aux1⟩, rhs := bodyNet.root }]
        root := ⟨rootIdx, .principal⟩ }
  | .bridge body =>
      let bodyNet := lower body
      let rootIdx := bodyNet.nodes.size
      { nodes := bodyNet.nodes.push (some { kind := .bridge, captures := #[bodyNet.root] })
        wires := bodyNet.wires ++ [{ lhs := ⟨rootIdx, .aux1⟩, rhs := bodyNet.root }]
        root := ⟨rootIdx, .principal⟩ }
  | .app fn arg =>
      let fnNet := lower fn
      let argNet := lower arg
      let argShift := fnNet.nodes.size
      let argRoot := argNet.root.shiftAgent argShift
      let argWires := argNet.wires.map (·.shiftAgent argShift)
      let argNodes := argNet.nodes.map (Option.map (fun node => shiftNode node argShift))
      let baseNodes := fnNet.nodes ++ argNodes
      let rootIdx := baseNodes.size
      { nodes := baseNodes.push (some { kind := .app, captures := #[fnNet.root, argRoot] })
        wires := fnNet.wires ++ argWires ++
          [ { lhs := ⟨rootIdx, .aux1⟩, rhs := fnNet.root }
          , { lhs := ⟨rootIdx, .aux2⟩, rhs := argRoot }
          ]
        root := ⟨rootIdx, .principal⟩ }
  | .ann val typ =>
      let valNet := lower val
      let typNet := lower typ
      let typShift := valNet.nodes.size
      let typRoot := typNet.root.shiftAgent typShift
      let typWires := typNet.wires.map (·.shiftAgent typShift)
      let typNodes := typNet.nodes.map (Option.map (fun node => shiftNode node typShift))
      let baseNodes := valNet.nodes ++ typNodes
      let rootIdx := baseNodes.size
      { nodes := baseNodes.push (some { kind := .ann, captures := #[valNet.root, typRoot] })
        wires := valNet.wires ++ typWires ++
          [ { lhs := ⟨rootIdx, .aux1⟩, rhs := valNet.root }
          , { lhs := ⟨rootIdx, .aux2⟩, rhs := typRoot }
          ]
        root := ⟨rootIdx, .principal⟩ }

private def roleJson (role : PortRole) : Json :=
  Json.str <|
    match role with
    | .principal => "principal"
    | .aux1 => "aux1"
    | .aux2 => "aux2"

private def agentKindJson (kind : ICCAgent) : Json :=
  Json.str <|
    match kind with
    | .var => "var"
    | .lam => "lam"
    | .app => "app"
    | .bridge => "bridge"
    | .ann => "ann"
    | .dup => "dup"
    | .era => "era"

private def portJson (p : Port) : Json :=
  Json.mkObj
    [ ("agent", Json.num p.agent)
    , ("role", roleJson p.role)
    ]

private def agentJson (idx : Nat) (node : ICCNode) : Json :=
  Json.mkObj
    [ ("id", Json.num idx)
    , ("kind", agentKindJson node.kind)
    , ("captures", Json.arr (node.captures.toList.map portJson |>.toArray))
    , ("payload",
        match node.payload with
        | some payload => Json.num payload
        | none => Json.null)
    ]

private def wireJson (wire : Wire) : Json :=
  Json.mkObj
    [ ("lhs", portJson wire.lhs)
    , ("rhs", portJson wire.rhs)
    ]

def emitJson (net : ICCNet) : Json :=
  let agents :=
    (List.zip (List.range net.nodes.size) net.nodes.toList).foldl
      (fun acc entry =>
        match entry.2 with
        | some node => acc.push (agentJson entry.1 node)
        | none => acc)
      #[]
  Json.mkObj
    [ ("agents", Json.arr agents)
    , ("wires", Json.arr (net.wires.map wireJson |>.toArray))
    , ("root", portJson net.root)
    , ("active_pairs",
        Json.arr <| (net.activePairs.map fun (lhs, rhs) =>
          Json.arr #[Json.num lhs, Json.num rhs]).toArray)
    ]

end HeytingLean.Bridge.INet.ICC
