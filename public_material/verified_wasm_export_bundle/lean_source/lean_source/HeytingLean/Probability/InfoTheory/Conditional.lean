import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import HeytingLean.Probability.InfoTheory.KL
import HeytingLean.Probability.InfoTheory.MutualInfo

namespace HeytingLean
namespace Probability
namespace InfoTheory

noncomputable section

open scoped BigOperators

namespace FinDist

variable {α β : Type u} [Fintype α] [Fintype β]

/-!
Conditional distributions for finite (discrete) joints.

This is a proof-first, finite-only layer used by the Kelly “side information”
duality theorem. To keep the initial development proof-hole-free and simple, we work
under **full support** (`Pos`) hypotheses when we need to use `Real.log` laws.
-/

theorem nonempty_of_FinDist {γ : Type u} [Fintype γ] (P : FinDist γ) : Nonempty γ := by
  classical
  by_contra h
  haveI : IsEmpty γ := (not_nonempty_iff.1 h)
  have : (∑ x : γ, P.pmf x) = 0 := by simp
  have : (∑ x : γ, P.pmf x) = 1 := P.sum_one
  linarith

theorem marginalLeft_pos_of_Pos (PXY : FinDist (α × β)) (hP : PXY.Pos) :
    (marginalLeft (α := α) (β := β) PXY).Pos := by
  classical
  let PA := marginalLeft (α := α) (β := β) PXY
  haveI : Nonempty β :=
    ⟨(nonempty_of_FinDist (γ := α × β) PXY).some.2⟩
  intro a
  have : 0 < (∑ b : β, PXY.pmf (a, b)) := by
    simpa using
      (Finset.sum_pos (s := (Finset.univ : Finset β))
        (f := fun b : β => PXY.pmf (a, b))
        (by intro b hb; exact hP (a, b))
        (Finset.univ_nonempty : (Finset.univ : Finset β).Nonempty))
  simpa [PA, marginalLeft] using this

theorem marginalRight_pos_of_Pos (PXY : FinDist (α × β)) (hP : PXY.Pos) :
    (marginalRight (α := α) (β := β) PXY).Pos := by
  classical
  let PB := marginalRight (α := α) (β := β) PXY
  haveI : Nonempty α :=
    ⟨(nonempty_of_FinDist (γ := α × β) PXY).some.1⟩
  intro b
  have : 0 < (∑ a : α, PXY.pmf (a, b)) := by
    simpa using
      (Finset.sum_pos (s := (Finset.univ : Finset α))
        (f := fun a : α => PXY.pmf (a, b))
        (by intro a ha; exact hP (a, b))
        (Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty))
  simpa [PB, marginalRight] using this

def condDistOfPos (PXY : FinDist (α × β)) (hP : PXY.Pos) (a : α) : FinDist β :=
  let PA := marginalLeft (α := α) (β := β) PXY
  let hPApos : 0 < PA.pmf a := (marginalLeft_pos_of_Pos (α := α) (β := β) PXY hP) a
  { pmf := fun b => PXY.pmf (a, b) / PA.pmf a
    nonneg := by
      intro b
      have hpab : 0 ≤ PXY.pmf (a, b) := PXY.nonneg (a, b)
      have hpa : 0 ≤ PA.pmf a := le_of_lt hPApos
      exact div_nonneg hpab hpa
    sum_one := by
      classical
      have hpa0 : PA.pmf a ≠ 0 := ne_of_gt hPApos
      calc
        (∑ b : β, PXY.pmf (a, b) / PA.pmf a)
            = (∑ b : β, PXY.pmf (a, b)) / PA.pmf a := by
                simp [div_eq_mul_inv, Finset.sum_mul]
        _ = PA.pmf a / PA.pmf a := by rfl
        _ = 1 := by simp [hpa0] }

theorem condDistOfPos_pmf_mul_marginalLeft (PXY : FinDist (α × β)) (hP : PXY.Pos) (ab : α × β) :
    (marginalLeft (α := α) (β := β) PXY).pmf ab.1
        * (condDistOfPos (α := α) (β := β) PXY hP ab.1).pmf ab.2
      = PXY.pmf ab := by
  classical
  let PA := marginalLeft (α := α) (β := β) PXY
  have hPApos : 0 < PA.pmf ab.1 := (marginalLeft_pos_of_Pos (α := α) (β := β) PXY hP) ab.1
  have hPA0 : PA.pmf ab.1 ≠ 0 := ne_of_gt hPApos
  -- `PA(a) * (PXY(a,b)/PA(a)) = (PA(a) * PXY(a,b)) / PA(a) = PXY(a,b)`.
  calc
    PA.pmf ab.1 * (condDistOfPos (α := α) (β := β) PXY hP ab.1).pmf ab.2
        = PA.pmf ab.1 * (PXY.pmf ab / PA.pmf ab.1) := by
            simp [condDistOfPos, PA]
    _ = PA.pmf ab.1 * PXY.pmf ab / PA.pmf ab.1 := by
            simp [div_eq_mul_inv, mul_assoc]
    _ = PXY.pmf ab := by
            simpa using (mul_div_cancel_left₀ (M₀ := ℝ) (b := PXY.pmf ab) (a := PA.pmf ab.1) hPA0)

theorem mutualInfo_eq_sum_mul_log_ratio_of_Pos (PXY : FinDist (α × β)) (hP : PXY.Pos) :
    mutualInfo (α := α) (β := β) PXY
      = ∑ ab : α × β,
          PXY.pmf ab * Real.log (PXY.pmf ab / ((marginalLeft (α := α) (β := β) PXY).pmf ab.1
            * (marginalRight (α := α) (β := β) PXY).pmf ab.2)) := by
  classical
  let PA := marginalLeft (α := α) (β := β) PXY
  let PB := marginalRight (α := α) (β := β) PXY
  have hPApos : PA.Pos := marginalLeft_pos_of_Pos (α := α) (β := β) PXY hP
  have hPBpos : PB.Pos := marginalRight_pos_of_Pos (α := α) (β := β) PXY hP
  have hprodpos : (prod PA PB).Pos := by
    intro ab
    exact mul_pos (hPApos ab.1) (hPBpos ab.2)
  -- Expand KL using the general lemma, then rewrite `log(p/q)` as `log p - log q`.
  have hkl :
      klDiv PXY (prod PA PB)
        = ∑ ab : α × β, PXY.pmf ab * (Real.log (PXY.pmf ab) - Real.log ((prod PA PB).pmf ab)) := by
    simpa [PA, PB] using (klDiv_eq_sum_mul_log_sub_of_Pos (P := PXY) (Q := prod PA PB) hP hprodpos)
  -- `log(p/q) = log p - log q` under positivity.
  have hlogdiv :
      ∀ ab : α × β,
        Real.log (PXY.pmf ab / (PA.pmf ab.1 * PB.pmf ab.2))
          = Real.log (PXY.pmf ab) - Real.log (PA.pmf ab.1 * PB.pmf ab.2) := by
    intro ab
    have hp : 0 < PXY.pmf ab := hP ab
    have hq : 0 < PA.pmf ab.1 * PB.pmf ab.2 := mul_pos (hPApos ab.1) (hPBpos ab.2)
    simpa [div_eq_mul_inv] using (Real.log_div (ne_of_gt hp) (ne_of_gt hq))
  -- And `prod`'s pmf is the product of marginals.
  have hprod : ∀ ab : α × β, (prod PA PB).pmf ab = PA.pmf ab.1 * PB.pmf ab.2 := by intro ab; rfl
  calc
    mutualInfo (α := α) (β := β) PXY
        = klDiv PXY (prod PA PB) := by rfl
    _ = ∑ ab : α × β, PXY.pmf ab * (Real.log (PXY.pmf ab) - Real.log (PA.pmf ab.1 * PB.pmf ab.2)) := by
          simpa [hprod] using hkl
    _ = ∑ ab : α × β, PXY.pmf ab * Real.log (PXY.pmf ab / (PA.pmf ab.1 * PB.pmf ab.2)) := by
          refine Finset.sum_congr rfl ?_
          intro ab _
          symm
          simpa using congrArg (fun t => PXY.pmf ab * t) (hlogdiv ab)
    _ = ∑ ab : α × β,
          PXY.pmf ab * Real.log (PXY.pmf ab / (PA.pmf ab.1 * PB.pmf ab.2)) := rfl

end FinDist

end

end InfoTheory
end Probability
end HeytingLean
