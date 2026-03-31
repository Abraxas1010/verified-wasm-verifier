import HeytingLean.Probability.InfoTheory.Conditional
import HeytingLean.Probability.InfoTheory.MutualInfo

namespace HeytingLean
namespace Economics
namespace Kelly
namespace Advanced

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory
open HeytingLean.Probability.InfoTheory.FinDist

variable {α β : Type u} [Fintype α] [Fintype β]

/-- A minimal “resource theory” interface: a set of resources with a family of allowed operations. -/
structure ResourceTheory where
  Resource : Type
  Op : Type
  apply : Op → Resource → Resource

/-- A real-valued resource monotone for a given resource theory. -/
def IsResourceMonotone (T : ResourceTheory) (M : T.Resource → ℝ) : Prop :=
  ∀ op r, M (T.apply op r) ≤ M r

/-! ### Correlation as a resource (finite discrete) -/

/-- Erase all correlation in a joint distribution, keeping the same marginals. -/
def eraseCorrelation (PXY : FinDist (α × β)) : FinDist (α × β) :=
  prod (marginalLeft (α := α) (β := β) PXY) (marginalRight (α := α) (β := β) PXY)

lemma marginalLeft_prod_pmf (P : FinDist α) (Q : FinDist β) (a : α) :
    (marginalLeft (α := α) (β := β) (prod P Q)).pmf a = P.pmf a := by
  classical
  calc
    (marginalLeft (α := α) (β := β) (prod P Q)).pmf a
        = ∑ b : β, P.pmf a * Q.pmf b := by
            simp [FinDist.marginalLeft, FinDist.prod]
    _ = P.pmf a * (∑ b : β, Q.pmf b) := by
            simp [Finset.mul_sum]
    _ = P.pmf a := by
            simp [Q.sum_one]

lemma marginalRight_prod_pmf (P : FinDist α) (Q : FinDist β) (b : β) :
    (marginalRight (α := α) (β := β) (prod P Q)).pmf b = Q.pmf b := by
  classical
  calc
    (marginalRight (α := α) (β := β) (prod P Q)).pmf b
        = ∑ a : α, P.pmf a * Q.pmf b := by
            simp [FinDist.marginalRight, FinDist.prod]
    _ = (∑ a : α, P.pmf a) * Q.pmf b := by
            simp [Finset.sum_mul]
    _ = Q.pmf b := by
            simp [P.sum_one]

theorem mutualInfo_eraseCorrelation_zero (PXY : FinDist (α × β)) :
    mutualInfo (α := α) (β := β) (eraseCorrelation (α := α) (β := β) PXY) = 0 := by
  classical
  let PA := marginalLeft (α := α) (β := β) PXY
  let PB := marginalRight (α := α) (β := β) PXY
  let P0 : FinDist (α × β) := prod PA PB
  have hpmf :
      ∀ ab : α × β,
        (prod
            (marginalLeft (α := α) (β := β) P0)
            (marginalRight (α := α) (β := β) P0)).pmf ab = P0.pmf ab := by
    intro ab
    have hL : (marginalLeft (α := α) (β := β) P0).pmf ab.1 = PA.pmf ab.1 := by
      simpa [P0] using (marginalLeft_prod_pmf (α := α) (β := β) PA PB ab.1)
    have hR : (marginalRight (α := α) (β := β) P0).pmf ab.2 = PB.pmf ab.2 := by
      simpa [P0] using (marginalRight_prod_pmf (α := α) (β := β) PA PB ab.2)
    calc
      (prod (marginalLeft (α := α) (β := β) P0) (marginalRight (α := α) (β := β) P0)).pmf ab
          = (marginalLeft (α := α) (β := β) P0).pmf ab.1
              * (marginalRight (α := α) (β := β) P0).pmf ab.2 := by
              rfl
      _ = PA.pmf ab.1 * PB.pmf ab.2 := by
              simp [hL, hR]
      _ = P0.pmf ab := by
              rfl
  unfold FinDist.mutualInfo eraseCorrelation
  have hkl :
      klDiv P0
          (prod (marginalLeft (α := α) (β := β) P0) (marginalRight (α := α) (β := β) P0))
        = klDiv P0 P0 := by
    refine klDiv_congr_right (α := α × β) (P := P0) (Q₁ := _)
      (Q₂ := P0) ?_
    exact hpmf
  -- reduce to `klDiv P0 P0 = 0`.
  rw [hkl]
  exact FinDist.klDiv_self_zero (α := α × β) P0

theorem mutualInfo_eraseCorrelation_le_of_Pos (PXY : FinDist (α × β)) (hP : PXY.Pos) :
    mutualInfo (α := α) (β := β) (eraseCorrelation (α := α) (β := β) PXY)
      ≤ mutualInfo (α := α) (β := β) PXY := by
  have h0 : mutualInfo (α := α) (β := β) (eraseCorrelation (α := α) (β := β) PXY) = 0 :=
    mutualInfo_eraseCorrelation_zero (α := α) (β := β) PXY
  have hPApos : (marginalLeft (α := α) (β := β) PXY).Pos :=
    marginalLeft_pos_of_Pos (α := α) (β := β) PXY hP
  have hPBpos : (marginalRight (α := α) (β := β) PXY).Pos :=
    marginalRight_pos_of_Pos (α := α) (β := β) PXY hP
  have hprodpos :
      (prod (marginalLeft (α := α) (β := β) PXY) (marginalRight (α := α) (β := β) PXY)).Pos := by
    intro ab
    exact mul_pos (hPApos ab.1) (hPBpos ab.2)
  have hnonneg : 0 ≤ mutualInfo (α := α) (β := β) PXY :=
    mutualInfo_nonneg_of_Pos (α := α) (β := β) PXY hprodpos
  simpa [h0] using hnonneg

end

end Advanced
end Kelly
end Economics
end HeytingLean
