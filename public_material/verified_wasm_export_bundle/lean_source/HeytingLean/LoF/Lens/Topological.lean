import Mathlib/Topology/Basic

open scoped Classical Topology

namespace HeytingLean.LoF.Lens.Topological

variable {X : Type _} [TopologicalSpace X]

/-- Topological interior as meet‑preserving "hull". -/
def I (s : Set X) : Set X := interior s

@[simp] lemma subset (s : Set X) : I s ⊆ s := interior_subset

lemma monotone {s t : Set X} (h : s ⊆ t) : I s ⊆ I t := interior_mono h

@[simp] lemma idempotent (s : Set X) : I (I s) = I s := by
  simpa [I] using interior_interior (s := s)

@[simp] lemma inf_preserving (s t : Set X) : I (s ∩ t) = I s ∩ I t := by
  simpa [I] using interior_inter (s := s) (t := t)

end HeytingLean.LoF.Lens.Topological

