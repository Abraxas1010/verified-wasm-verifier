import HeytingLean.LeanClef.DTS.AbelianGroup

/-!
# LeanClef.DTS.Persistence

Formalize and prove that dimensional annotations are preserved
through compilation stages.

Reference: Haynes arXiv:2603.16437, Section 2.3
-/

namespace LeanClef.DTS

/-- A term carrying a dimension annotation. -/
structure AnnotatedTerm (α : Type) (n : Nat) where
  term : α
  dim : Dimension n

/-- A transformation preserves dimensions. -/
def DimPreserving {α : Type} {n : Nat} (f : AnnotatedTerm α n → AnnotatedTerm α n) : Prop :=
  ∀ t, (f t).dim = t.dim

/-- Apply a pipeline left-to-right (recursive for clean induction). -/
def applyPipeline {α : Type} {n : Nat} :
    List (AnnotatedTerm α n → AnnotatedTerm α n) → AnnotatedTerm α n → AnnotatedTerm α n
  | [], t => t
  | f :: rest, t => applyPipeline rest (f t)

/-- If every stage preserves dimensions, the whole pipeline preserves dimensions. -/
theorem pipeline_preserves_dim {α : Type} {n : Nat}
    (pipeline : List (AnnotatedTerm α n → AnnotatedTerm α n))
    (h : ∀ f, f ∈ pipeline → DimPreserving f)
    (t : AnnotatedTerm α n) :
    (applyPipeline pipeline t).dim = t.dim := by
  induction pipeline generalizing t with
  | nil => rfl
  | cons f rest ih =>
    show (applyPipeline rest (f t)).dim = t.dim
    have h_dp : DimPreserving f := h f (.head rest)
    have h_rest : ∀ g, g ∈ rest → DimPreserving g :=
      fun g hg => h g (.tail f hg)
    exact (ih h_rest (f t)).trans (h_dp t)

/-- Composing two dimension-preserving pipelines preserves dimensions. -/
theorem pipeline_compose_preserves_dim {α : Type} {n : Nat}
    (p1 p2 : List (AnnotatedTerm α n → AnnotatedTerm α n))
    (h1 : ∀ f, f ∈ p1 → DimPreserving f)
    (h2 : ∀ f, f ∈ p2 → DimPreserving f)
    (t : AnnotatedTerm α n) :
    (applyPipeline (p1 ++ p2) t).dim = t.dim := by
  apply pipeline_preserves_dim
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact h1 f h
  · exact h2 f h

end LeanClef.DTS
