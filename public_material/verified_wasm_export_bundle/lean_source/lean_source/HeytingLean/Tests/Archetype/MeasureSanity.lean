import HeytingLean.Measure.README
import HeytingLean.Bridges.Archetype.MeasureToAdelic

open MeasureTheory

example {α : Type} [MeasurableSpace α] (μ : Measure α) (s t : Set α) (hsub : s ⊆ t) :
    μ s ≤ μ t := by
  exact HeytingLean.Measure.measure_mono_set μ hsub

example {α : Type} [MeasurableSpace α] (μ : Measure α) :
    μ (∅ : Set α) = 0 := by
  exact HeytingLean.Measure.measure_empty_zero μ

example {α : Type} [MeasurableSpace α] (μ : Measure α) :
    (μ (∅ : Set α) = 0) ∧
      (HeytingLean.Metrics.Magnitude.finiteMagnitude PEmpty = 0) := by
  exact HeytingLean.Measure.measure_empty_matches_magnitude_zero μ

example (x : ∀ t, HeytingLean.Embeddings.coreLensData.Completion t) :
    {t : HeytingLean.Embeddings.CoreLensTag |
      x t ∉ HeytingLean.Embeddings.coreLensData.Integral t}.Finite := by
  exact HeytingLean.Measure.coreLens_nonintegral_support_finite x

example {α : Type} [MeasurableSpace α] (μ : Measure α)
    (x : ∀ t, HeytingLean.Embeddings.coreLensData.Completion t) :
    μ (∅ : Set α) = 0 ∧
      {t : HeytingLean.Embeddings.CoreLensTag |
        x t ∉ HeytingLean.Embeddings.coreLensData.Integral t}.Finite := by
  exact HeytingLean.Bridges.Archetype.measure_to_adelic_zero_mass_and_finite_support μ x
