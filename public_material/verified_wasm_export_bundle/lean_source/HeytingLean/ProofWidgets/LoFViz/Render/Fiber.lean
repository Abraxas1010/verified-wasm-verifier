import HeytingLean.ProofWidgets.LoFViz.State
import HeytingLean.ProofWidgets.LoFViz.Kernel
import HeytingLean.ProofWidgets.LoFViz.Render.Types

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz
namespace Render

/-- Choose a colour palette based on a boolean status. -/
@[inline] def statusColour (okColor warnColor : String) (flag : Bool) : String :=
  if flag then okColor else warnColor

/-- Build an SVG view showing the base LoF manifold with three bridge fibres. -/
def fiberSvg (kernel : KernelData) : String :=
  let base :=
    "<svg viewBox='0 0 420 240' xmlns='http://www.w3.org/2000/svg'>
      <rect x='2' y='2' width='416' height='236' rx='24' fill='#0f172a' stroke='#1e293b' stroke-width='3'/>
      <defs>
        <linearGradient id='fiberGrad' x1='0%' y1='0%' x2='100%' y2='100%'>
          <stop offset='0%' stop-color='#22d3ee'/>
          <stop offset='100%' stop-color='#4338ca'/>
        </linearGradient>
        <marker id='arrowTip' markerWidth='10' markerHeight='10' refX='10' refY='5' orient='auto'>
          <path d='M0,0 L10,5 L0,10 z' fill='#22d3ee'/>
        </marker>
      </defs>"
  let status := kernel.fiberStatus
  let logicColour := statusColour "#22d3ee" "#f87171" status.logicStable
  let tensorColour := statusColour "#0284c7" "#facc15" status.tensorBounded
  let graphColour := statusColour "#22c55e" "#fb7185" status.graphActivated
  let cliffordColour := statusColour "#a855f7" "#f97316" status.cliffordEven
  let currentCard := kernel.currentCard
  let baseManifold :=
    s!"<circle cx='210' cy='150' r='{40 + currentCard * 8}' fill='rgba(15,118,110,0.25)' stroke='{statusColour "#0f766e" "#fb7185" status.logicStable}' stroke-width='4'/>
       <text x='210' y='120' text-anchor='middle' font-family='monospace' font-size='13' fill='#ccfbf1'>LoF Core (Ω_R)</text>
       <text x='210' y='170' text-anchor='middle' font-family='monospace' font-size='11' fill='#94a3b8'>|regions| = {currentCard}</text>"
  let stageNote :=
    s!"<text x='210' y='188' text-anchor='middle' font-family='monospace' font-size='10' fill='#38bdf8'>{KernelData.stageTransportNote}</text>"
  let fiberBoxes :=
    s!"<rect x='40' y='42' width='110' height='70' rx='16' fill='rgba(2,132,199,0.18)' stroke='{logicColour}' stroke-width='3'/>
       <rect x='170' y='20' width='110' height='70' rx='16' fill='rgba(234,179,8,0.18)' stroke='{tensorColour}' stroke-width='3'/>
       <rect x='300' y='42' width='110' height='70' rx='16' fill='rgba(217,70,239,0.18)' stroke='{cliffordColour}' stroke-width='3'/>"
  let fiberLabels :=
    s!"<text x='95' y='78' text-anchor='middle' font-family='monospace' font-size='12' fill='#bae6fd'>Logic fibre ({if status.logicStable then "stable" else "drifting"})</text>
       <text x='225' y='55' text-anchor='middle' font-family='monospace' font-size='12' fill='#fde68a'>Tensor fibre ({if status.tensorBounded then "bounded" else "overflow"})</text>
       <text x='355' y='78' text-anchor='middle' font-family='monospace' font-size='12' fill='#f5d0fe'>Clifford fibre ({if status.cliffordEven then "even" else "odd"})</text>"
  let arrows :=
    s!"<path d='M95 112 L185 140' stroke='{tensorColour}' stroke-width='4' fill='none' marker-end='url(#arrowTip)' opacity='0.85'/>
       <path d='M225 90 L225 120' stroke='{graphColour}' stroke-width='4' fill='none' marker-end='url(#arrowTip)' opacity='0.85'/>
       <path d='M355 112 L245 140' stroke='{cliffordColour}' stroke-width='4' fill='none' marker-end='url(#arrowTip)' opacity='0.85'/>"
  let footer :=
    s!"<text x='210' y='228' text-anchor='middle' font-family='monospace' font-size='12' fill='#94a3b8'>{kernel.summary}</text>"
  base ++ baseManifold ++ stageNote ++ fiberBoxes ++ fiberLabels ++ arrows ++ footer ++ "</svg>"

/-- Render the fiber bundle portal. -/
def renderFiber (state : State) (kernel : KernelData) : BridgeResult :=
  let hud : Hud :=
    { dialStage := state.dialStage
      lens := state.lens
      mode := state.mode
      notes := kernel.notes ++ kernel.fiberNotes }
  BridgeResult.mk (fiberSvg kernel) hud kernel.certificates

end Render
end LoFViz
end ProofWidgets
end HeytingLean
