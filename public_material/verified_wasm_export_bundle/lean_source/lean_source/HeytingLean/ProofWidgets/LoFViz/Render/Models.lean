import HeytingLean.ProofWidgets.LoFViz.State
import HeytingLean.ProofWidgets.LoFViz.Kernel

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz
namespace Render

/-- Data backing the Boundary/Euler visualization. -/
structure BoundaryModel where
  mode            : VisualMode
  currentCard     : Nat
  previousCard    : Nat
  currentRadius   : Nat
  previousRadius  : Nat
  showEuler       : Bool
  currentActive   : Bool
  previousActive  : Bool
  summary         : String
  deriving Inhabited, Repr

/-- Extract boundary-specific data from a kernel snapshot. -/
def BoundaryModel.fromKernel (kernel : KernelData) (mode : VisualMode) : BoundaryModel :=
  { mode := mode
    currentCard := kernel.currentCard
    previousCard := kernel.previousCard
    currentRadius := 24 + kernel.currentCard * 10
    previousRadius := 36 + kernel.previousCard * 8
    showEuler := mode = .euler
    currentActive := kernel.currentIsActive
    previousActive := kernel.previousIsActive
    summary := kernel.summary }

@[simp] lemma BoundaryModel.currentRadius_spec (kernel : KernelData) (mode : VisualMode) :
    (BoundaryModel.fromKernel kernel mode).currentRadius = 24 + kernel.currentCard * 10 := rfl

@[simp] lemma BoundaryModel.previousRadius_spec (kernel : KernelData) (mode : VisualMode) :
    (BoundaryModel.fromKernel kernel mode).previousRadius = 36 + kernel.previousCard * 8 := rfl

@[simp] lemma BoundaryModel.currentActive_spec (kernel : KernelData) (mode : VisualMode) :
    (BoundaryModel.fromKernel kernel mode).currentActive = kernel.currentIsActive := rfl

@[simp] lemma BoundaryModel.previousActive_spec (kernel : KernelData) (mode : VisualMode) :
    (BoundaryModel.fromKernel kernel mode).previousActive = kernel.previousIsActive := rfl

/-- Nodes displayed in the hypergraph renderer. -/
inductive HyperNode
  | process
  | current
  | previous
  | euler
  | counter
  deriving DecidableEq, Inhabited, Repr

/-- Directed edges between hypergraph nodes. -/
structure HyperEdge where
  src         : HyperNode
  tgt         : HyperNode
  highlighted : Bool
  deriving DecidableEq, Inhabited, Repr

/-- Data backing the hypergraph visualization. -/
structure HypergraphModel where
  currentActive               : Bool
  previousActive              : Bool
  reentryCount                : Nat
  reentryHighlighted          : Bool
  processToCurrentHighlighted : Bool
  previousToCurrentEdge       : Bool
  currentLabel                : String
  previousLabel               : String
  reentryLabel                : String
  summary                     : String
  edges                       : List HyperEdge
  deriving Inhabited, Repr

/-- Extract hypergraph-specific data from a kernel snapshot. -/
def HypergraphModel.fromKernel (kernel : KernelData) : HypergraphModel :=
  let reentryHighlighted := decide (0 < kernel.aggregate.reentries)
  let previousActive := kernel.previousIsActive
  let previousLabel :=
    if previousActive then s!"previous {kernel.previousSetString}" else "previous (∅)"
  let currentLabel :=
    if kernel.currentIsActive then s!"current {kernel.currentSetString}" else "current (∅)"
  let reentryLabel :=
    if kernel.aggregate.reentries = 0 then "no re-entry"
    else s!"re-entry ×{kernel.aggregate.reentries}"
  let baseEdges : List HyperEdge :=
    [ { src := .process, tgt := .current, highlighted := kernel.currentIsActive }
    , { src := .process, tgt := .euler, highlighted := kernel.currentIsActive }
    , { src := .euler, tgt := .current, highlighted := reentryHighlighted }
    , { src := .euler, tgt := .counter, highlighted := reentryHighlighted }
    , { src := .process, tgt := .counter, highlighted := true } ]
  let edges :=
    if previousActive then
      baseEdges ++ [ { src := .previous, tgt := .current, highlighted := true } ]
    else baseEdges
  { currentActive := kernel.currentIsActive
    previousActive
    reentryCount := kernel.aggregate.reentries
    reentryHighlighted
    processToCurrentHighlighted := kernel.currentIsActive
    previousToCurrentEdge := previousActive
    currentLabel
    previousLabel
    reentryLabel
    summary := kernel.summary
    edges }

@[simp] lemma HypergraphModel.currentActive_spec (kernel : KernelData) :
    (HypergraphModel.fromKernel kernel).currentActive = kernel.currentIsActive := rfl

@[simp] lemma HypergraphModel.previousActive_spec (kernel : KernelData) :
    (HypergraphModel.fromKernel kernel).previousActive = kernel.previousIsActive := rfl

@[simp] lemma HypergraphModel.reentryCount_spec (kernel : KernelData) :
    (HypergraphModel.fromKernel kernel).reentryCount = kernel.aggregate.reentries := rfl

@[simp] lemma HypergraphModel.reentryHighlighted_spec (kernel : KernelData) :
    (HypergraphModel.fromKernel kernel).reentryHighlighted = decide (0 < kernel.aggregate.reentries) := rfl

@[simp] lemma boundary_hypergraph_current_coupling (kernel : KernelData) (mode : VisualMode) :
    (BoundaryModel.fromKernel kernel mode).currentActive =
      (HypergraphModel.fromKernel kernel).currentActive := rfl

@[simp] lemma boundary_hypergraph_previous_coupling (kernel : KernelData) (mode : VisualMode) :
    (BoundaryModel.fromKernel kernel mode).previousActive =
      (HypergraphModel.fromKernel kernel).previousActive := rfl

end Render
end LoFViz
end ProofWidgets
end HeytingLean
