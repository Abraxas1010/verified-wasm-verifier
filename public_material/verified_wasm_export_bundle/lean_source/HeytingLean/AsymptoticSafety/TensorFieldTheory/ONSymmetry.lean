import HeytingLean.AsymptoticSafety.CouplingSpace

namespace HeytingLean
namespace AsymptoticSafety
namespace TensorFieldTheory

structure TensorTruncation where
  orderN : Nat
  screening : ℝ
  antiscreening : ℝ
  quarticFixedPoint : ℝ
  source : String

def tensorVolume (τ : TensorTruncation) : Nat := τ.orderN ^ 3

theorem tensorVolume_pos (τ : TensorTruncation) (hN : 0 < τ.orderN) :
    0 < tensorVolume τ := by
  simpa [tensorVolume] using pow_pos hN 3

end TensorFieldTheory
end AsymptoticSafety
end HeytingLean
