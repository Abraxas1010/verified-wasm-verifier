import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace HeytingLean
namespace Measure

open MeasureTheory

theorem measure_union_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s t : Set α) :
    μ (s ∪ t) ≤ μ s + μ t := by
  simpa using measure_union_le s t

theorem measure_empty_zero {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    μ ∅ = 0 := by
  simp

theorem measure_mono_set {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s t : Set α} (hsub : s ⊆ t) :
    μ s ≤ μ t := by
  exact measure_mono hsub

theorem measure_inter_le_left {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s t : Set α) :
    μ (s ∩ t) ≤ μ s := by
  exact measure_mono Set.inter_subset_left

end Measure
end HeytingLean
