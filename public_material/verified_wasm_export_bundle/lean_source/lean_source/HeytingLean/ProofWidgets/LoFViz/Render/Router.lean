import Lean
import HeytingLean.ProofWidgets.LoFViz.State
import HeytingLean.ProofWidgets.LoFViz.Kernel
import HeytingLean.ProofWidgets.LoFViz.Render.Types
import HeytingLean.ProofWidgets.LoFViz.Render.Models
import HeytingLean.ProofWidgets.LoFViz.Render.Boundary
import HeytingLean.ProofWidgets.LoFViz.Render.Hypergraph
import HeytingLean.ProofWidgets.LoFViz.Render.Fiber
import HeytingLean.ProofWidgets.LoFViz.Render.String

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz
namespace Render

open Lean

/-- Simple SVG fallback for modes not yet implemented. -/
def demoSvg (state : State) (kernel : KernelData) : BridgeResult :=
  let label := toString state.mode
  let svg :=
    s!"<svg viewBox='0 0 360 200' xmlns='http://www.w3.org/2000/svg'>
        <rect x='2' y='2' width='356' height='196' rx='20' fill='#111827' stroke='#1f2937' stroke-width='3'/>
        <text x='180' y='90' fill='#e5e7eb' text-anchor='middle' font-family='monospace' font-size='18'>{label}</text>
        <text x='180' y='125' fill='#9ca3af' text-anchor='middle' font-family='monospace' font-size='12'>{kernel.summary}</text>
      </svg>"
  { svg
    hud :=
      { dialStage := state.dialStage
        lens := state.lens
        mode := state.mode
        notes := kernel.notes }
    certificates := kernel.certificates }

/-- Build a simple boundary-style panel for split mode. -/
def splitBoundaryPanel (model : BoundaryModel) : String :=
  s!"<rect x='24' y='22' width='320' height='176' rx='18' fill='rgba(14,116,144,0.15)' stroke='#0ea5e9' stroke-width='2'/>
     <text x='184' y='48' text-anchor='middle' font-family='monospace' font-size='15' fill='#38bdf8'>Boundary View</text>
     <circle cx='184' cy='120' r='64' fill='rgba(56,189,248,0.18)' stroke='#38bdf8' stroke-width='4'/>
     <circle cx='184' cy='120' r='{model.currentRadius}' fill='#38bdf829' stroke='#0ea5e9' stroke-width='4'/>
     <text x='184' y='174' text-anchor='middle' font-family='monospace' font-size='12' fill='#e0f2fe'>{model.summary}</text>"

/-- Build a hypergraph-style panel for split mode. -/
def splitHypergraphPanel (model : HypergraphModel) : String :=
  s!"<rect x='24' y='22' width='320' height='176' rx='18' fill='rgba(139,92,246,0.15)' stroke='#8b5cf6' stroke-width='2'/>
     <text x='184' y='48' text-anchor='middle' font-family='monospace' font-size='15' fill='#c4b5fd'>Hypergraph View</text>
     <circle cx='84' cy='150' r='22' fill='rgba(168,85,247,0.2)' stroke='#c084fc' stroke-width='3'/>
     <text x='84' y='152' text-anchor='middle' font-family='monospace' font-size='11' fill='#f5d0fe'>{model.previousLabel}</text>
     <circle cx='184' cy='110' r='28' fill='rgba(56,189,248,0.2)' stroke='#38bdf8' stroke-width='3'/>
     <text x='184' y='112' text-anchor='middle' font-family='monospace' font-size='11' fill='#bae6fd'>current</text>
     <circle cx='284' cy='80' r='22' fill='rgba(34,197,94,0.2)' stroke='#22c55e' stroke-width='3'/>
     <text x='284' y='82' text-anchor='middle' font-family='monospace' font-size='11' fill='#bbf7d0'>process</text>
     <text x='184' y='174' text-anchor='middle' font-family='monospace' font-size='12' fill='#ddd6fe'>{model.reentryLabel}</text>"

/-- Combined split-mode SVG showing boundary and hypergraph side-by-side. -/
def splitSvg (boundaryModel : BoundaryModel) (hyperModel : HypergraphModel) : String :=
  s!"<svg viewBox='0 0 740 220' xmlns='http://www.w3.org/2000/svg'>
      <rect x='2' y='2' width='736' height='216' rx='24' fill='#0b1120' stroke='#1e293b' stroke-width='3'/>
      <g transform='translate(0,0)'>
        {splitBoundaryPanel boundaryModel}
      </g>
      <g transform='translate(360,0)'>
        {splitHypergraphPanel hyperModel}
      </g>
      <text x='370' y='198' text-anchor='middle' font-family='monospace' font-size='11' fill='#94a3b8'>{hyperModel.previousLabel}</text>
      <text x='370' y='214' text-anchor='middle' font-family='monospace' font-size='11' fill='#64748b'>{hyperModel.summary}</text>
    </svg>"

/-- Route a render request for the selected mode. -/
def route (state : State) (kernel : KernelData) : BridgeResult :=
  match state.mode with
  | .boundary   => renderBoundary state kernel
  | .euler      => renderBoundary state kernel
  | .hypergraph => renderHypergraph state kernel
  | .fiber      => renderFiber state kernel
  | .string     => renderString state kernel
  | .split      =>
      let boundaryModel := BoundaryModel.fromKernel kernel .boundary
      let hyperModel := HypergraphModel.fromKernel kernel
      let hud : Hud :=
        { dialStage := state.dialStage
          lens := state.lens
          mode := state.mode
          notes :=
            kernel.notes ++
              #["Left panel: boundary containment.",
                "Right panel: hypergraph merges journal ordering."] }
      BridgeResult.mk (splitSvg boundaryModel hyperModel) hud kernel.certificates

end Render
end LoFViz
end ProofWidgets
end HeytingLean
