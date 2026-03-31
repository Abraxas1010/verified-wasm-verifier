import HeytingLean.Probability.InfoTheory.Entropy
import HeytingLean.Probability.InfoTheory.KL

namespace HeytingLean
namespace Probability
namespace InfoTheory

noncomputable section

open scoped BigOperators

namespace FinDist

variable {α β : Type u} [Fintype α] [Fintype β]

def mutualInfo (PXY : FinDist (α × β)) : ℝ :=
  klDiv PXY (prod (marginalLeft (α := α) (β := β) PXY) (marginalRight (α := α) (β := β) PXY))

theorem mutualInfo_nonneg_of_Pos (PXY : FinDist (α × β))
    (hprod : (prod (marginalLeft (α := α) (β := β) PXY) (marginalRight (α := α) (β := β) PXY)).Pos) :
    0 ≤ mutualInfo (α := α) (β := β) PXY := by
  simpa [mutualInfo] using
    (klDiv_nonneg_of_Pos (P := PXY)
      (Q := prod (marginalLeft (α := α) (β := β) PXY) (marginalRight (α := α) (β := β) PXY))
      hprod)

end FinDist

end

end InfoTheory
end Probability
end HeytingLean

