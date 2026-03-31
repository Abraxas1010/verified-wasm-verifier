import HeytingLean.Measure.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

open MeasureTheory

theorem measure_to_adelic_finite_nonintegral_support
    (x : ∀ t, Embeddings.coreLensData.Completion t) :
    {t : Embeddings.CoreLensTag | x t ∉ Embeddings.coreLensData.Integral t}.Finite := by
  exact Measure.coreLens_nonintegral_support_finite x

theorem measure_to_adelic_zero_mass_and_finite_support
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (x : ∀ t, Embeddings.coreLensData.Completion t) :
    μ (∅ : Set α) = 0 ∧
      {t : Embeddings.CoreLensTag | x t ∉ Embeddings.coreLensData.Integral t}.Finite := by
  constructor
  · exact Measure.measure_empty_zero μ
  · exact measure_to_adelic_finite_nonintegral_support x

end Archetype
end Bridges
end HeytingLean
