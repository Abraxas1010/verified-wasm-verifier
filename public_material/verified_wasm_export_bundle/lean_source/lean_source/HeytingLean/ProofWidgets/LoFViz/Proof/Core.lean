import Lean
import Lean.Elab.Command
import ProofWidgets.Data.Html
import HeytingLean.ProofWidgets.LoFViz.State
import HeytingLean.ProofWidgets.LoFViz.Kernel
import HeytingLean.ProofWidgets.LoFViz.Render.Types
import HeytingLean.ProofWidgets.LoFViz.Render.Router
import HeytingLean.ProofWidgets.LoFViz.Proof.Graph

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz
namespace Proof

open Lean
open Lean Elab Command
open Graph
open Kernel

def defaultFuel : Nat := 128

private def stringToName (s : String) : Except String Name :=
  let parts := s.splitOn "."
  match parts with
  | [] => .error "empty constant name"
  | hd :: tl =>
      let rec go : Name → List String → Name
        | name, [] => name
        | name, h :: t =>
            go (Name.str name h) t
      let base := Name.mkSimple hd
      .ok <| go base tl

def nameFromString? (s : String) : Option Name :=
  (stringToName s).toOption

/-- Render a compact label for an expression node. -/
private def exprLabel (e : Expr) : String :=
  match e with
  | .const n _   => s!"const {n}"
  | .lam n _ _ _ => s!"λ {n}"
  | .forallE n _ _ _ => s!"∀ {n}"
  | .app ..      => "app"
  | .letE n _ _ _ _ => s!"let {n}"
  | .proj _ idx _ => s!"proj #{idx}"
  | .mvar id     => s!"?{id.name}"
  | .fvar id     => s!"fvar {id.name}"
  | .sort u      => s!"Sort {u}"
  | .lit (.natVal v) => s!"nat {v}"
  | .lit (.strVal v) => s!"str \"{v}\""
  | .bvar idx    => s!"bvar {idx}"
  | _            => toString e

private def constNameOf : Expr → Option Name
  | .const n _ => some n
  | _          => none

abbrev TermBuildM := StateM ProofGraph

private def pushNodeM (node : Node) : TermBuildM NodeId := do
  let g ← get
  let (g', id) := ProofGraph.pushNode g node
  set g'
  pure id

private def pushEdgeM (edge : Edge) : TermBuildM Unit :=
  modify fun g => ProofGraph.pushEdge g edge

def buildTermGraph (fuel depth : Nat) (e : Expr) : TermBuildM NodeId := do
  match fuel with
  | 0 =>
      pushNodeM
        { kind := .term
          depth
          label := "… (fuel exhausted)" }
  | fuel + 1 =>
      let id ← pushNodeM
        { kind := .term
          depth
          label := exprLabel e
          const? := constNameOf e }
      let next := fuel
      match e with
      | .app f x => do
          let fId ← buildTermGraph next (depth + 1) f
          pushEdgeM { src := id, dst := fId, kind := .dependency, label := "fn" }
          let xId ← buildTermGraph next (depth + 1) x
          pushEdgeM { src := id, dst := xId, kind := .dependency, label := "arg" }
          pure id
      | .lam _ ty body _ => do
          let tyId ← buildTermGraph next (depth + 1) ty
          pushEdgeM { src := id, dst := tyId, kind := .dependency, label := "type" }
          let bodyId ← buildTermGraph next (depth + 1) body
          pushEdgeM { src := id, dst := bodyId, kind := .dependency, label := "body" }
          pure id
      | .forallE _ ty body _ => do
          let tyId ← buildTermGraph next (depth + 1) ty
          pushEdgeM { src := id, dst := tyId, kind := .dependency, label := "domain" }
          let bodyId ← buildTermGraph next (depth + 1) body
          pushEdgeM { src := id, dst := bodyId, kind := .dependency, label := "codomain" }
          pure id
      | .letE _ _ value body _ => do
          let valueId ← buildTermGraph next (depth + 1) value
          pushEdgeM { src := id, dst := valueId, kind := .dependency, label := "value" }
          let bodyId ← buildTermGraph next (depth + 1) (body.instantiate1 value)
          pushEdgeM { src := id, dst := bodyId, kind := .dependency, label := "body" }
          pure id
      | .mdata _ inner => do
          let innerId ← buildTermGraph next depth inner
          pushEdgeM { src := id, dst := innerId, kind := .dependency, label := "meta" }
          pure id
      | .proj _ _ inner => do
          let innerId ← buildTermGraph next (depth + 1) inner
          pushEdgeM { src := id, dst := innerId, kind := .dependency, label := "proj" }
          pure id
      | _ => pure id

def primitiveKind : Primitive → PrimitiveKind
  | .mark   => .mark
  | .unmark => .unmark
  | .reentry => .reentry

def primitiveLabel : Primitive → String
  | .mark    => "Mark"
  | .unmark  => "Unmark"
  | .reentry => "Re-entry"

private def regionArray (s : List String) : Array String :=
  s.toArray

def journalGraph (sceneId : String) (journal : Array Primitive)
    (graph : ProofGraph) : ProofGraph × NodeId := Id.run do
  let initAgg := Aggregate.empty
  let initLabel := s!"state[0] ({sceneId}) {RegionSet.toString initAgg.current}"
  let (graph, initStateId) :=
    ProofGraph.pushNode graph
      { id := 0
        kind := .state
        depth := 0
        label := initLabel
        region := regionArray initAgg.current }
  let (agg, graph, _, _) :=
    journal.foldl
      (fun (acc :
          Aggregate × ProofGraph × NodeId × Nat) prim =>
        let (agg, g, prevStateId, stepIx) := acc
        let label := s!"{stepIx}: {primitiveLabel prim}"
        let (g, primId) :=
          ProofGraph.pushNode g
            { id := 0
              kind := .primitive
              depth := stepIx
              label
              journalIx := some stepIx
              primitive := some (primitiveKind prim) }
        let g := ProofGraph.pushEdge g
          { src := prevStateId
            dst := primId
            kind := .journal
            label := "step" }
        let agg' := Aggregate.step agg prim
        let stateLabel := s!"state[{stepIx + 1}] ({sceneId}) {RegionSet.toString agg'.current}"
        let (g, stateId) :=
          ProofGraph.pushNode g
            { id := 0
              kind := .state
              depth := stepIx + 1
              label := stateLabel
              region := regionArray agg'.current
              journalIx := some (stepIx + 1) }
        let g := ProofGraph.pushEdge g
          { src := primId
            dst := stateId
            kind := .journal
            label := primitiveLabel prim }
        (agg', g, stateId, stepIx + 1))
      (initAgg, graph, initStateId, 0)
  let graph :=
    if graph.root.isNone then { graph with root := some initStateId } else graph
  (graph, initStateId)

def buildProofGraph (sceneId : String) (journal : Array Primitive)
    (proof : Expr) : ProofGraph :=
  let (termRoot, termGraph) :=
    (buildTermGraph defaultFuel 0 proof).run {}
  let baseGraph := { termGraph with root := some termRoot }
  let (graphWithJournal, initialStateId) :=
    journalGraph sceneId journal baseGraph
  let graphWithLens :=
    ProofGraph.pushEdge graphWithJournal
      { src := termRoot
        dst := initialStateId
        kind := .lens
        label := "proof-root" }
  graphWithLens

/-- Metadata describing the proof being visualised. -/
structure Handle where
  name       : Name
  statement  : String
  provenance : String := "declaration"
  deriving Inhabited

/-- LoF journal obtained from a proof. -/
structure Normalized where
  handle      : Handle
  journal     : Array Primitive
  graph       : Graph.ProofGraph := {}
  annotations : Array String := #[]
  deriving Inhabited

/-- Fully rendered bundle combining all visuals. -/
structure VisualizationBundle where
  handle  : Handle
  state   : State
  kernel  : KernelData
  graph   : Graph.ProofGraph
  renders : Array (VisualMode × Render.BridgeResult)
  summary : Render.ApplyResponse

def visitExpr (root : Name) (fuel : Nat) (e : Expr) :
    StateM (Array Primitive) Unit := do
  match fuel with
  | 0 => pure ()
  | fuel + 1 =>
      match e with
      | Expr.lam _ _ body _ => do
          modify fun xs => xs.push Primitive.mark
          visitExpr root fuel body
          modify fun xs => xs.push Primitive.unmark
      | Expr.forallE _ _ body _ => do
          modify fun xs => xs.push Primitive.mark
          visitExpr root fuel body
          modify fun xs => xs.push Primitive.unmark
      | Expr.app f x => do
          let fn := f.getAppFn
          if fn.isConst then
            let cname := fn.constName!
            if cname == root then
              modify fun xs => xs.push Primitive.reentry
          visitExpr root fuel f
          visitExpr root fuel x
      | Expr.letE _ _ value body _ => do
          visitExpr root fuel value
          visitExpr root fuel (body.instantiate1 value)
      | Expr.mdata _ inner =>
          visitExpr root fuel inner
      | Expr.proj _ _ inner =>
          visitExpr root fuel inner
      | _ => pure ()

def constantProofExpr? : ConstantInfo → Option Expr
  | ConstantInfo.thmInfo thm     => some thm.value
  | ConstantInfo.opaqueInfo info => some info.value
  | ConstantInfo.defnInfo info   => some info.value
  | _                            => none

def Normalized.ofConstantCore (name : Name) (fuel := defaultFuel) :
    CoreM Normalized := do
  let env ← getEnv
  let some info := env.find? name
    | throwError "Unknown declaration {name}."
  let some proofTerm := constantProofExpr? info
    | throwError "Declaration {name} does not carry a proof term."
  let stmt := toString info.type
  let (_, journal) := (visitExpr name fuel proofTerm).run #[]
  let graph := buildProofGraph (toString name) journal proofTerm
  let journal :=
    if journal.isEmpty then
      #[Primitive.mark, Primitive.reentry, Primitive.unmark]
    else
      journal
  pure
    { handle :=
        { name
          statement := stmt
          provenance := s!"declaration {name}" }
      journal
      graph
      annotations := #[
        s!"LoF journal length: {journal.size}"
      ] }

def Normalized.ofConstant (name : Name) (fuel := defaultFuel) :
    CommandElabM Normalized := do
  liftCoreM <| Normalized.ofConstantCore name fuel

def applyJournal (sceneId : String) (journal : Array Primitive) : State :=
  journal.foldl (fun acc prim => Stepper.applyPrimitive acc prim) (initialState sceneId)

def Normalized.toState (p : Normalized) : State :=
  let scene :=
    if p.handle.name == Name.anonymous then
      p.handle.statement
    else
      toString p.handle.name
  applyJournal scene p.journal

def renderAll (state : State) : Array (VisualMode × Render.BridgeResult) :=
  let modes := #[VisualMode.boundary, VisualMode.hypergraph, VisualMode.fiber, VisualMode.string, VisualMode.split]
  modes.map fun mode =>
    let s := { state with mode := mode }
    (mode, Render.route s (KernelData.fromState s))

def Normalized.toBundle (p : Normalized) : VisualizationBundle :=
  let state := p.toState
  let kernel := KernelData.fromState state
  let renders := renderAll state
  let defaultRender :=
    (renders.findSome? fun
      | (VisualMode.boundary, res) => some res
      | _ => none).getD (Render.route state kernel)
  { handle := p.handle
    state
    kernel
    graph := p.graph
    renders
    summary :=
      { render :=
          { sceneId := state.sceneId
            stage := toString state.dialStage
            lens := toString state.lens
            svg := defaultRender.svg
            hud := defaultRender.hud }
        proof := defaultRender.certificates } }

def bundleOfConstantCore (name : Name) (fuel := defaultFuel) : CoreM VisualizationBundle := do
  let norm ← Normalized.ofConstantCore name fuel
  pure norm.toBundle

def bundleOfConstant (name : Name) (fuel := defaultFuel) : CommandElabM VisualizationBundle := do
  liftCoreM <| bundleOfConstantCore name fuel

def graphJsonOfConstant (name : Name) (fuel := defaultFuel) : CommandElabM Json := do
  let bundle ← bundleOfConstant name fuel
  pure (bundle.graph.toJson)

private def describePrimitive : Primitive → String
  | Primitive.unmark => "Unmark"
  | Primitive.mark   => "Mark"
  | Primitive.reentry => "Re-entry"

def renderBlock (mode : VisualMode) (result : Render.BridgeResult) : ProofWidgets.Html :=
  let svgPayload := Json.mkObj [("__html", Json.str result.svg)]
  let attrs : Array (String × Json) :=
    #[("className", Json.str "lof-svg"), ("dangerouslySetInnerHTML", svgPayload)]
  let notes :=
    result.hud.notes.map fun note =>
      ProofWidgets.Html.element "li" #[] #[ProofWidgets.Html.text note]
  ProofWidgets.Html.element "div" #[] #[
    ProofWidgets.Html.element "h3" #[] #[ProofWidgets.Html.text (toString mode)],
    ProofWidgets.Html.element "div" attrs #[],
    ProofWidgets.Html.element "ul" #[] notes
  ]

def journalBlock (bundle : VisualizationBundle) : ProofWidgets.Html :=
  let entries :=
    bundle.state.journal.map fun entry =>
      ProofWidgets.Html.element "li" #[] #[ProofWidgets.Html.text s!"{entry.timestamp}: {describePrimitive entry.primitive}"]
  ProofWidgets.Html.element "div" #[] #[
    ProofWidgets.Html.element "h3" #[] #[ProofWidgets.Html.text "LoF Journal"],
    ProofWidgets.Html.element "ol" #[] entries
  ]

def VisualizationBundle.toHtml (bundle : VisualizationBundle) : ProofWidgets.Html :=
  let renderNodes :=
    bundle.renders.map (fun (mode, res) => renderBlock mode res)
  let graphJson := Json.compress (bundle.graph.toJson)
  let graphScript :=
    ProofWidgets.Html.element "script"
      #[("type", Json.str "application/json"), ("id", Json.str "lof-proof-graph")]
      #[ProofWidgets.Html.text graphJson]
  ProofWidgets.Html.element "div" #[]
    (#[
        ProofWidgets.Html.element "header" #[] #[
          ProofWidgets.Html.element "h2" #[] #[ProofWidgets.Html.text bundle.handle.statement],
          ProofWidgets.Html.element "p"  #[] #[ProofWidgets.Html.text bundle.handle.provenance]
        ],
        ProofWidgets.Html.element "section" #[] #[journalBlock bundle],
        ProofWidgets.Html.element "section" #[] renderNodes,
        graphScript
      ])

def htmlOfConstant (name : Name) : CommandElabM ProofWidgets.Html := do
  let bundle ← bundleOfConstant name
  pure (bundle.toHtml)

end Proof
end LoFViz
end ProofWidgets
end HeytingLean
