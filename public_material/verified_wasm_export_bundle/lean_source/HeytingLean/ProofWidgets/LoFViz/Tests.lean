import HeytingLean.ProofWidgets.LoFViz.State
import HeytingLean.ProofWidgets.LoFViz.Kernel
import HeytingLean.ProofWidgets.LoFViz.Render.Models

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz

lemma kernelSummary_ne_empty (s : State) :
    (KernelData.fromState s).summary ≠ "" := by
  simp [KernelData.fromState]

lemma certificates_have_default_message (s : State) :
    (KernelData.certificates (KernelData.fromState s)).messages ≠ #[] := by
  simp [KernelData.certificates]

lemma notes_nonempty (s : State) :
    (KernelData.fromState s).notes ≠ #[] := by
  simp [KernelData.fromState, KernelData.notes]

lemma fiberNotes_length (s : State) :
    (KernelData.fiberNotes (KernelData.fromState s)).length = 5 := by
  simp [KernelData.fromState, KernelData.fiberNotes]

lemma fiberNotes_contains_transport (s : State) :
    KernelData.stageTransportNote ∈
      (KernelData.fiberNotes (KernelData.fromState s)).toList := by
  simp [KernelData.fromState, KernelData.fiberNotes, KernelData.stageTransportNote]

lemma boundary_and_hypergraph_share_activity (s : State) :
    let kernel := KernelData.fromState s
    (BoundaryModel.fromKernel kernel .boundary).currentActive =
      (HypergraphModel.fromKernel kernel).currentActive := by
  intro kernel
  simp [boundary_hypergraph_current_coupling]

lemma boundary_radius_formula (s : State) :
    let kernel := KernelData.fromState s
    (BoundaryModel.fromKernel kernel .boundary).currentRadius =
      24 + kernel.currentCard * 10 := by
  intro kernel
  simp

lemma hypergraph_reentry_matches_kernel (s : State) :
    let kernel := KernelData.fromState s
    (HypergraphModel.fromKernel kernel).reentryCount = kernel.aggregate.reentries := by
  intro kernel
  simp

end LoFViz
end ProofWidgets
end HeytingLean
