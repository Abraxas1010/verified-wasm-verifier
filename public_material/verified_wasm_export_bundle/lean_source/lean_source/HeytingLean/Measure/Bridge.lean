import HeytingLean.Measure.Basic
import HeytingLean.Metrics.Magnitude.Basic
import HeytingLean.Embeddings.AdelicInstances

namespace HeytingLean
namespace Measure

open MeasureTheory

theorem coreLens_nonintegral_support_finite
    (x : ∀ t, Embeddings.coreLensData.Completion t) :
    {t : Embeddings.CoreLensTag | x t ∉ Embeddings.coreLensData.Integral t}.Finite := by
  simpa using (Embeddings.PerspectivalDescentCarrier.finiteness
    (Carrier := Embeddings.coreLensData.Completion) x)

theorem measure_empty_matches_magnitude_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) :
    (μ (∅ : Set α) = 0) ∧ (Metrics.Magnitude.finiteMagnitude PEmpty = 0) := by
  constructor
  · exact measure_empty_zero μ
  · exact Metrics.Magnitude.finiteMagnitude_empty

end Measure
end HeytingLean
