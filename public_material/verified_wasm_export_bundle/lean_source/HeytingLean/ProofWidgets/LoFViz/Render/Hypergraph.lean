import HeytingLean.ProofWidgets.LoFViz.State
import HeytingLean.ProofWidgets.LoFViz.Kernel
import HeytingLean.ProofWidgets.LoFViz.Render.Types
import HeytingLean.ProofWidgets.LoFViz.Render.Models

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz
namespace Render

/-- SVG utility: draw a node circle with label. -/
def nodeSvg (x y radius : Nat) (label : String) (active : Bool) : String :=
  let fill := if active then "#22d3ee" else "rgba(34,211,238,0.15)"
  let stroke := if active then "#0891b2" else "#334155"
  s!"<g>
      <circle cx='{x}' cy='{y}' r='{radius}'
        fill='{fill}' stroke='{stroke}' stroke-width='3'/>
      <text x='{x}' y='{y + radius + 18}'
        fill='#e2e8f0' text-anchor='middle'
        font-family='monospace' font-size='12'>{label}</text>
    </g>"

/-- SVG utility: draw a directed edge. -/
def edgeSvg (x₁ y₁ x₂ y₂ : Nat) (highlight : Bool) : String :=
  let color := if highlight then "#f97316" else "#475569"
  s!"<line x1='{x₁}' y1='{y₁}' x2='{x₂}' y2='{y₂}'
        stroke='{color}' stroke-width='3' marker-end='url(#arrow)' opacity='0.85'/>"

/-- Build the hypergraph SVG from the kernel aggregate. -/
def hypergraphSvg (model : HypergraphModel) : String :=
  let background :=
    "<svg viewBox='0 0 360 220' xmlns='http://www.w3.org/2000/svg'>
      <defs>
        <marker id='arrow' markerWidth='10' markerHeight='10' refX='10' refY='5' orient='auto'>
          <path d='M0,0 L10,5 L0,10 z' fill='#f97316' />
        </marker>
      </defs>
      <rect x='2' y='2' width='356' height='216' rx='20'
        fill='#0f172a' stroke='#1e293b' stroke-width='3'/>"
  let processNode := nodeSvg 90 70 28 "process (⊤)" true
  let currentLabel :=
    model.currentLabel
  let currentNode := nodeSvg 180 140 30 currentLabel model.currentActive
  let previousLabel := model.previousLabel
  let previousNode :=
    if model.previousActive then
      nodeSvg 70 180 24 previousLabel model.previousActive
    else ""
  let eulerNode :=
    nodeSvg 270 80 26 "Euler boundary" true
  let counterNode :=
    nodeSvg 280 170 24 "counter (⊤)" true
  let edges :=
    let baseEdges :=
      [edgeSvg 90 98 175 130 model.processToCurrentHighlighted,
       edgeSvg 270 106 190 136 model.reentryHighlighted,
       edgeSvg 270 100 270 146 model.reentryHighlighted,
       edgeSvg 90 98 270 84 model.processToCurrentHighlighted,
       edgeSvg 90 98 280 166 true]
    let prevEdge :=
      if model.previousActive then
        [edgeSvg 94 166 170 148 model.previousToCurrentEdge]
      else []
    String.intercalate "" (baseEdges ++ prevEdge)
  let title :=
    s!"<text x='180' y='26' fill='#e2e8f0' text-anchor='middle' font-family='monospace' font-size='16'>Re-entry Hypergraph</text>"
  let subtitle :=
    s!"<text x='180' y='210' fill='#94a3b8' text-anchor='middle' font-family='monospace' font-size='12'>{model.summary}</text>"
  background ++ processNode ++ eulerNode ++ counterNode ++ currentNode ++ previousNode
    ++ edges ++ title ++ subtitle ++ "</svg>"

/-- Render the hypergraph mode. -/
def renderHypergraph (state : State) (kernel : KernelData) : BridgeResult :=
  let model := HypergraphModel.fromKernel kernel
  let hud : Hud :=
    { dialStage := state.dialStage
      lens := state.lens
      mode := state.mode
      notes :=
        kernel.notes ++
          #["Hypergraph edges show re-entry dependencies.",
            if model.reentryCount > 0 then
              "Purple edges highlight re-entry events."
            else "No re-entry recorded, dependency graph is acyclic for the journal."] }
  BridgeResult.mk (hypergraphSvg model) hud kernel.certificates

end Render
end LoFViz
end ProofWidgets
end HeytingLean
