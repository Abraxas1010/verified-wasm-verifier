import HeytingLean.ProofWidgets.LoFViz.State
import HeytingLean.ProofWidgets.LoFViz.Kernel
import HeytingLean.ProofWidgets.LoFViz.Render.Types
import HeytingLean.ProofWidgets.LoFViz.Render.Models

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz
namespace Render

open Lean

/-- Helper to craft an SVG circle element. -/
def circle (cx cy r : Nat) (fill stroke : String) (opacity : String := "1") : String :=
  s!"<circle cx='{cx}' cy='{cy}' r='{r}' fill='{fill}' stroke='{stroke}' stroke-width='3' opacity='{opacity}'/>"

/-- Render the boundary/euler visualization using the canonical LoF nucleus. -/
def boundarySvg (model : BoundaryModel) : String :=
  let baseFill := if model.currentActive then "#38bdf8" else "rgba(56,189,248,0.15)"
  let prevStroke := if model.previousActive then "#f97316" else "rgba(249,115,22,0.3)"
  let eulerStroke := if model.showEuler then "#facc15" else "#3b82f6"
  let background :=
    "<rect x='2' y='2' width='356' height='196' rx='20' fill='#0f172a' stroke='#1e293b' stroke-width='3'/>"
  let eulerCircle :=
    circle 180 100 80 "none" eulerStroke (if model.showEuler then "1" else "0.35")
  let previousCircle :=
    if model.previousActive then
      circle 180 100 model.previousRadius "none" prevStroke "0.55"
    else ""
  let currentCircle :=
    circle 180 100 model.currentRadius baseFill "#0ea5e9" "0.85"
  let label :=
    s!"<text x='180' y='32' fill='#e2e8f0' text-anchor='middle' font-family='monospace' font-size='16'>{if model.showEuler then "Euler Boundary" else "Boundary Kernel"}</text>"
  let subtitle :=
    s!"<text x='180' y='190' fill='#94a3b8' text-anchor='middle' font-family='monospace' font-size='12'>{model.summary}</text>"
  "<svg viewBox='0 0 360 200' xmlns='http://www.w3.org/2000/svg'>" ++ background ++ eulerCircle ++ previousCircle ++ currentCircle ++ label ++ subtitle ++ "</svg>"

/-- Render the boundary/euler mode. -/
def renderBoundary (state : State) (kernel : KernelData) : BridgeResult :=
  let model := BoundaryModel.fromKernel kernel state.mode
  let extra :=
    if state.mode = .euler then
      kernel.notes.push "Euler boundary is emphasised."
    else kernel.notes
  let hud : Hud :=
    { dialStage := state.dialStage
      lens := state.lens
      mode := state.mode
      notes := extra }
  let svg := boundarySvg model
  BridgeResult.mk svg hud kernel.certificates

end Render
end LoFViz
end ProofWidgets
end HeytingLean
