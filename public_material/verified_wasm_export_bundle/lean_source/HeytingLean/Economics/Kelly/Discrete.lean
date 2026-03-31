import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import HeytingLean.Probability.InfoTheory

namespace HeytingLean
namespace Economics
namespace Kelly

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

variable {Outcome : Type u} [Fintype Outcome]

def oddsTerm (p : FinDist Outcome) (odds : Outcome → ℝ) : ℝ :=
  ∑ x : Outcome, p.pmf x * Real.log (odds x)

def growthRate (p b : FinDist Outcome) (odds : Outcome → ℝ) : ℝ :=
  ∑ x : Outcome, p.pmf x * Real.log (b.pmf x * odds x)

@[simp] lemma klDiv_self_zero (p : FinDist Outcome) :
    HeytingLean.Probability.InfoTheory.FinDist.klDiv p p = 0 := by
  classical
  unfold HeytingLean.Probability.InfoTheory.FinDist.klDiv
  refine Finset.sum_eq_zero ?_
  intro x _
  -- `klTerm p p = 0` for all `p`.
  by_cases hp : p.pmf x ≤ 0
  · simp [klTerm, hp]
  · have hp' : 0 < p.pmf x := lt_of_not_ge hp
    simp [klTerm, hp, safeLog_of_pos hp', sub_self]

lemma growthRate_eq_oddsTerm_sub_entropy_sub_kl_of_Pos
    (p b : FinDist Outcome) (odds : Outcome → ℝ)
    (hp : HeytingLean.Probability.InfoTheory.FinDist.Pos p)
    (hb : HeytingLean.Probability.InfoTheory.FinDist.Pos b)
    (hodds : ∀ x, 0 < odds x) :
    growthRate p b odds
      = oddsTerm p odds
        - HeytingLean.Probability.InfoTheory.FinDist.entropy p
        - HeytingLean.Probability.InfoTheory.FinDist.klDiv p b := by
  classical
  have hlogmul :
      ∀ x : Outcome, Real.log (b.pmf x * odds x) = Real.log (b.pmf x) + Real.log (odds x) := by
    intro x
    have hb' : 0 < b.pmf x := hb x
    have ho' : 0 < odds x := hodds x
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.log_mul (ne_of_gt hb') (ne_of_gt ho'))
  have hsplitGrowth :
      growthRate p b odds
        = (∑ x : Outcome, p.pmf x * Real.log (b.pmf x))
          + (∑ x : Outcome, p.pmf x * Real.log (odds x)) := by
    unfold growthRate
    simp [hlogmul, mul_add, Finset.sum_add_distrib]
  have hkldef :=
    HeytingLean.Probability.InfoTheory.FinDist.klDiv_eq_sum_mul_log_sub_of_Pos (P := p) (Q := b) hp hb
  have hkl :
      (∑ x : Outcome, p.pmf x * Real.log (b.pmf x))
        = (∑ x : Outcome, p.pmf x * Real.log (p.pmf x))
          - HeytingLean.Probability.InfoTheory.FinDist.klDiv p b := by
    have hsplit :
        HeytingLean.Probability.InfoTheory.FinDist.klDiv p b
          = (∑ x : Outcome, p.pmf x * Real.log (p.pmf x))
            - (∑ x : Outcome, p.pmf x * Real.log (b.pmf x)) := by
      calc
        HeytingLean.Probability.InfoTheory.FinDist.klDiv p b
            = ∑ x : Outcome, p.pmf x * (Real.log (p.pmf x) - Real.log (b.pmf x)) := hkldef
        _ = ∑ x : Outcome, (p.pmf x * Real.log (p.pmf x) - p.pmf x * Real.log (b.pmf x)) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              ring
        _ = (∑ x : Outcome, p.pmf x * Real.log (p.pmf x))
              - (∑ x : Outcome, p.pmf x * Real.log (b.pmf x)) := by
              simp [Finset.sum_sub_distrib]
    linarith
  have hent := HeytingLean.Probability.InfoTheory.FinDist.entropy_eq_neg_sum_mul_log_of_Pos (P := p) hp
  calc
    growthRate p b odds
        = (∑ x : Outcome, p.pmf x * Real.log (b.pmf x))
          + (∑ x : Outcome, p.pmf x * Real.log (odds x)) := hsplitGrowth
    _ = ((∑ x : Outcome, p.pmf x * Real.log (p.pmf x))
          - HeytingLean.Probability.InfoTheory.FinDist.klDiv p b)
          + (∑ x : Outcome, p.pmf x * Real.log (odds x)) := by simp [hkl]
    _ = (∑ x : Outcome, p.pmf x * Real.log (odds x))
          - (- (∑ x : Outcome, p.pmf x * Real.log (p.pmf x)))
          - HeytingLean.Probability.InfoTheory.FinDist.klDiv p b := by ring
    _ = oddsTerm p odds
          - HeytingLean.Probability.InfoTheory.FinDist.entropy p
          - HeytingLean.Probability.InfoTheory.FinDist.klDiv p b := by
          simp [oddsTerm, hent]

theorem growthRate_le_oddsTerm_sub_entropy
    (p b : FinDist Outcome) (odds : Outcome → ℝ)
    (hp : HeytingLean.Probability.InfoTheory.FinDist.Pos p)
    (hb : HeytingLean.Probability.InfoTheory.FinDist.Pos b)
    (hodds : ∀ x, 0 < odds x) :
    growthRate p b odds
      ≤ oddsTerm p odds - HeytingLean.Probability.InfoTheory.FinDist.entropy p := by
  have hdecomp :=
    growthRate_eq_oddsTerm_sub_entropy_sub_kl_of_Pos
      (p := p) (b := b) (odds := odds) hp hb hodds
  have hkl : 0 ≤ HeytingLean.Probability.InfoTheory.FinDist.klDiv p b :=
    HeytingLean.Probability.InfoTheory.FinDist.klDiv_nonneg_of_Pos (P := p) (Q := b) hb
  linarith [hdecomp, hkl]

theorem growthRate_eq_oddsTerm_sub_entropy_at_true
    (p : FinDist Outcome) (odds : Outcome → ℝ)
    (hp : HeytingLean.Probability.InfoTheory.FinDist.Pos p) (hodds : ∀ x, 0 < odds x) :
    growthRate p p odds = oddsTerm p odds - HeytingLean.Probability.InfoTheory.FinDist.entropy p := by
  have hdecomp :=
    growthRate_eq_oddsTerm_sub_entropy_sub_kl_of_Pos
      (p := p) (b := p) (odds := odds) hp hp hodds
  simpa [klDiv_self_zero] using hdecomp

theorem growthRate_le_at_true
    (p b : FinDist Outcome) (odds : Outcome → ℝ)
    (hp : HeytingLean.Probability.InfoTheory.FinDist.Pos p)
    (hb : HeytingLean.Probability.InfoTheory.FinDist.Pos b)
    (hodds : ∀ x, 0 < odds x) :
    growthRate p b odds ≤ growthRate p p odds := by
  have h₁ : growthRate p b odds ≤ oddsTerm p odds - HeytingLean.Probability.InfoTheory.FinDist.entropy p :=
    growthRate_le_oddsTerm_sub_entropy (p := p) (b := b) (odds := odds) hp hb hodds
  have h₂ : growthRate p p odds = oddsTerm p odds - HeytingLean.Probability.InfoTheory.FinDist.entropy p :=
    growthRate_eq_oddsTerm_sub_entropy_at_true (p := p) (odds := odds) hp hodds
  linarith [h₁, h₂]

end

end Kelly
end Economics
end HeytingLean
