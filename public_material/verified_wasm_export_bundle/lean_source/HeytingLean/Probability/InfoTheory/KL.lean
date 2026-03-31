import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Probability
namespace InfoTheory

noncomputable section

open scoped BigOperators

namespace FinDist

variable {α : Type u} [Fintype α]

def klDiv (P Q : FinDist α) : ℝ :=
  ∑ a : α, klTerm (P.pmf a) (Q.pmf a)

@[simp] theorem klDiv_self_zero (P : FinDist α) : klDiv P P = 0 := by
  classical
  unfold klDiv
  refine Finset.sum_eq_zero ?_
  intro a _
  by_cases hp : P.pmf a ≤ 0
  · simp [klTerm, hp]
  · have hp' : 0 < P.pmf a := lt_of_not_ge hp
    simp [klTerm, hp, safeLog_of_pos hp', sub_self]

theorem klDiv_congr_right (P : FinDist α) {Q₁ Q₂ : FinDist α} (h : ∀ a, Q₁.pmf a = Q₂.pmf a) :
    klDiv P Q₁ = klDiv P Q₂ := by
  classical
  unfold klDiv
  refine Finset.sum_congr rfl ?_
  intro a _
  simp [h a]

theorem klDiv_eq_sum_mul_log_sub_of_Pos (P Q : FinDist α) (hP : P.Pos) (hQ : Q.Pos) :
    klDiv P Q = ∑ a : α, P.pmf a * (Real.log (P.pmf a) - Real.log (Q.pmf a)) := by
  classical
  unfold klDiv
  refine Finset.sum_congr rfl ?_
  intro a _
  have hp : 0 < P.pmf a := hP a
  have hq : 0 < Q.pmf a := hQ a
  have hp_not_le : ¬ P.pmf a ≤ 0 := not_le_of_gt hp
  simp [klTerm, hp_not_le, safeLog_of_pos hp, safeLog_of_pos hq, sub_eq_add_neg]

lemma klTerm_ge_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p - q ≤ klTerm p q := by
  by_cases hp0 : p = 0
  · subst hp0
    have hq' : 0 ≤ q := le_of_lt hq
    simpa [klTerm, sub_eq_add_neg] using (neg_nonpos.mpr hq')
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hp_not_le : ¬ p ≤ 0 := not_le_of_gt hp_pos
    have sp : safeLog p = Real.log p := by simp [safeLog, hp_pos]
    have sq : safeLog q = Real.log q := by simp [safeLog, hq]
    have hlog : Real.log (q / p) ≤ q / p - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hmul : (-p) * (q / p - 1) ≤ (-p) * Real.log (q / p) :=
      mul_le_mul_of_nonpos_left hlog (by linarith [hp_pos])
    have hleft : (-p) * (q / p - 1) = p - q := by
      field_simp [hp0]
      ring
    have hright :
        (-p) * Real.log (q / p) = klTerm p q := by
      have hlogdiv : Real.log (q / p) = Real.log q - Real.log p := by
        simpa [div_eq_mul_inv] using (Real.log_div (by linarith [hq]) (by linarith [hp_pos]))
      calc
        (-p) * Real.log (q / p) = (-p) * (Real.log q - Real.log p) := by simp [hlogdiv]
        _ = p * (Real.log p - Real.log q) := by ring
        _ = p * (safeLog p - safeLog q) := by simp [sp, sq]
        _ = klTerm p q := by simp [klTerm, hp_not_le]
    -- Combine
    simpa [hleft, hright] using hmul

theorem klDiv_nonneg_of_Pos (P Q : FinDist α) (hQ : Q.Pos) : 0 ≤ klDiv P Q := by
  classical
  -- Sum the pointwise lower bounds `p - q ≤ klTerm p q`.
  have hsum :
      (∑ a : α, (P.pmf a - Q.pmf a)) ≤ ∑ a : α, klTerm (P.pmf a) (Q.pmf a) := by
    refine Finset.sum_le_sum ?_
    intro a _
    exact klTerm_ge_sub (hp := P.nonneg a) (hq := hQ a)
  have hmass : (∑ a : α, (P.pmf a - Q.pmf a)) = 0 := by
    calc
      (∑ a : α, (P.pmf a - Q.pmf a))
          = (∑ a : α, P.pmf a) - (∑ a : α, Q.pmf a) := by
              simp [Finset.sum_sub_distrib]
      _ = 1 - 1 := by simp [P.sum_one, Q.sum_one]
      _ = 0 := by ring
  have : 0 ≤ ∑ a : α, klTerm (P.pmf a) (Q.pmf a) := by
    have h0 : 0 ≤ (∑ a : α, (P.pmf a - Q.pmf a)) := by simp [hmass]
    exact le_trans h0 hsum
  simpa [klDiv] using this

end FinDist

end

end InfoTheory
end Probability
end HeytingLean
