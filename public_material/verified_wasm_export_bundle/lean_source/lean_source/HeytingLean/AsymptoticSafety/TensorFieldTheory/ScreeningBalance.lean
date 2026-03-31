import HeytingLean.AsymptoticSafety.TensorFieldTheory.ONSymmetry

namespace HeytingLean
namespace AsymptoticSafety
namespace TensorFieldTheory

def screeningBalance (τ : TensorTruncation) : ℝ :=
  τ.antiscreening - τ.screening

def balanced (τ : TensorTruncation) : Prop :=
  screeningBalance τ = 0

theorem balanced_iff (τ : TensorTruncation) :
    balanced τ ↔ τ.antiscreening = τ.screening := by
  unfold balanced screeningBalance
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

end TensorFieldTheory
end AsymptoticSafety
end HeytingLean
