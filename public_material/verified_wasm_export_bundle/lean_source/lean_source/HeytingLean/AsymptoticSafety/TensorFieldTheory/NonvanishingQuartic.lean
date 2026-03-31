import HeytingLean.AsymptoticSafety.TensorFieldTheory.ScreeningBalance

namespace HeytingLean
namespace AsymptoticSafety
namespace TensorFieldTheory

def fixedPointQuartic (τ : TensorTruncation) : ℝ :=
  τ.quarticFixedPoint + screeningBalance τ

def nonGaussianFixedPoint (τ : TensorTruncation) : Prop :=
  balanced τ ∧ fixedPointQuartic τ ≠ 0

theorem fixedPointQuartic_eq_quartic_of_balanced (τ : TensorTruncation)
    (hbal : balanced τ) :
    fixedPointQuartic τ = τ.quarticFixedPoint := by
  have hzero : screeningBalance τ = 0 := by
    simpa [balanced] using hbal
  simp [fixedPointQuartic, hzero]

theorem nonvanishingQuartic_of_nonzero (τ : TensorTruncation)
    (hbal : balanced τ)
    (hquartic : τ.quarticFixedPoint ≠ 0) :
    fixedPointQuartic τ ≠ 0 := by
  rw [fixedPointQuartic_eq_quartic_of_balanced τ hbal]
  exact hquartic

theorem balanced_nonGaussian_fixedPoint (τ : TensorTruncation)
    (hbal : balanced τ) (hquartic : τ.quarticFixedPoint ≠ 0) :
    nonGaussianFixedPoint τ := by
  exact ⟨hbal, nonvanishingQuartic_of_nonzero τ hbal hquartic⟩

end TensorFieldTheory
end AsymptoticSafety
end HeytingLean
