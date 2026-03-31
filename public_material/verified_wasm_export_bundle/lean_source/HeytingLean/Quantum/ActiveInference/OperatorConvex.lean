import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-
Helper lemmas about the scalar convexity of `x ↦ x log x`.  These will be
reused when lifting Jensen's inequality to density operators via spectral
decompositions, ensuring the analytic half of the CPTP monotonicity story is
available in finite dimensions.
-/

namespace HeytingLean
namespace Quantum
namespace ActiveInference

open scoped BigOperators

lemma convexCombo_mul_log_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : ∑ i ∈ s, w i = 1)
    (hx_nonneg : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * x i) * Real.log (∑ i ∈ s, w i * x i) ≤
      ∑ i ∈ s, w i * (x i * Real.log (x i)) := by
  classical
  have hmem : ∀ i ∈ s, x i ∈ Set.Ici (0 : ℝ) := fun i hi => by
    simpa [Set.mem_Ici] using hx_nonneg i hi
  have :=
    (Real.convexOn_mul_log.map_sum_le (t := s) (w := w) (p := fun i => x i)
        hw_nonneg hw_sum hmem)
  simpa [Set.mem_Ici, smul_eq_mul] using this

private lemma log_le_zero_of_pos_le_one {x : ℝ} (hx_pos : 0 < x) (hx_le : x ≤ 1) :
    Real.log x ≤ 0 := by
  have := Real.log_le_log hx_pos (by simpa using hx_le)
  simpa using this.trans_eq (by simp)

lemma sum_prob_log_le_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, p i * Real.log (p i) ≤ 0 := by
  classical
  have hterms :
      ∀ i ∈ s, p i * Real.log (p i) ≤ 0 := by
    intro i hi
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hp_pos : 0 < p i := lt_of_le_of_ne' (hp_nonneg i hi) hpi
      have hp_le_one : p i ≤ 1 :=
        (Finset.single_le_sum (fun j hj => hp_nonneg j hj) hi).trans_eq hp_sum
      have hlog : Real.log (p i) ≤ 0 :=
        log_le_zero_of_pos_le_one hp_pos hp_le_one
      exact mul_nonpos_of_nonneg_of_nonpos (hp_nonneg i hi) hlog
  have hsum :=
    Finset.sum_le_sum hterms
  simpa using hsum

lemma sum_mul_log_le_total {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    (hx_nonneg : ∀ i ∈ s, 0 ≤ x i) :
    ∑ i ∈ s, x i * Real.log (x i) ≤
      (∑ i ∈ s, x i) * Real.log (∑ i ∈ s, x i) := by
  classical
  set total := ∑ i ∈ s, x i
  have hx_sum_nonneg : 0 ≤ total :=
    Finset.sum_nonneg fun i hi => hx_nonneg i hi
  by_cases htotal_zero : total = 0
  · have hx_zero :
        ∀ i ∈ s, x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i hi => hx_nonneg i hi).1 htotal_zero
    have hsum_zero :
        (∑ i ∈ s, x i * Real.log (x i) : ℝ) = 0 := by
      classical
      have hconst :
          (∑ i ∈ s, x i * Real.log (x i) : ℝ) =
            ∑ i ∈ s, (0 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [hx_zero i hi]
      have hzero : ∑ i ∈ s, (0 : ℝ) = 0 := by simp
      exact hconst.trans hzero
    simp [hsum_zero, htotal_zero]
  · have htotal_pos : 0 < total := lt_of_le_of_ne' hx_sum_nonneg htotal_zero
    have htotal_ne : (total : ℝ) ≠ 0 := htotal_zero
    set p : ι → ℝ := fun i => x i / total
    have hx_mul_div : ∀ i, total * (x i / total) = x i := by
      intro i
      simpa using (mul_div_cancel₀ (x i) htotal_ne)
    have hmul_eq : ∀ i, total * p i = x i := by
      intro i
      simpa [p] using hx_mul_div i
    have hx_eq : ∀ i, x i = total * p i := fun i => (hmul_eq i).symm
    have hp_nonneg :
        ∀ i ∈ s, 0 ≤ p i := fun i hi =>
      div_nonneg (hx_nonneg i hi) htotal_pos.le
    have hp_sum :
        ∑ i ∈ s, p i = 1 := by
      have hdiv :=
        (Finset.sum_div (s := s) (f := fun i => x i) total).symm
      have hcalc : (∑ i ∈ s, x i) / total = 1 := by
        simp [total, htotal_ne]
      simpa [p, total, htotal_ne] using hdiv.trans hcalc
    have hcalc :
        ∀ i ∈ s,
          x i * Real.log (x i) =
            total * p i * Real.log total + total * p i * Real.log (p i) := by
      intro i hi
      by_cases hpi : p i = 0
      ·
        have hx_zero : x i = 0 := by
          simp [hx_eq i, hpi]
        simp [p, hpi, hx_zero]
      ·
        have hx_log' :
            Real.log (total * p i) = Real.log total + Real.log (p i) := by
          simpa using Real.log_mul htotal_ne hpi
        have hx_main :
            x i * Real.log (x i) =
              total * p i * Real.log (total * p i) := by
          simp [hx_eq i]
        have hx_split :
            total * p i * Real.log (total * p i) =
              total * (p i * (Real.log total + Real.log (p i))) := by
          have := congrArg (fun t => total * (p i * t)) hx_log'
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have hx_expand :
            total * (p i * (Real.log total + Real.log (p i))) =
              total * p i * Real.log total + total * p i * Real.log (p i) := by
          ring
        exact (hx_main.trans hx_split).trans hx_expand
    have hrewrite :
        ∑ i ∈ s, x i * Real.log (x i) =
          (∑ i ∈ s, total * p i * Real.log total) +
            (∑ i ∈ s, total * p i * Real.log (p i)) := by
      have :=
        Finset.sum_congr rfl fun i hi => hcalc i hi
      simpa [Finset.sum_add_distrib] using this
    have hfirst :
        ∑ i ∈ s, total * p i * Real.log total =
          (∑ i ∈ s, p i) * (total * Real.log total) := by
      have hterm :
          ∀ i, total * p i * Real.log total = p i * (total * Real.log total) := by
        intro i; ring
      have :=
        (Finset.sum_mul (s := s) (fun i : ι => p i) (total * Real.log total))
      simpa [hterm] using this.symm
    have hsecond :
        ∑ i ∈ s, total * p i * Real.log (p i) =
          (∑ i ∈ s, p i * Real.log (p i)) * total := by
      have hterm :
          ∀ i, total * p i * Real.log (p i) = (p i * Real.log (p i)) * total := by
        intro i; ring
      have :=
        (Finset.sum_mul (s := s) (fun i : ι => p i * Real.log (p i)) total)
      simpa [hterm] using this.symm
    have hsplit_main :
        ∑ i ∈ s, x i * Real.log (x i) =
          (∑ i ∈ s, p i) * (total * Real.log total) +
            (∑ i ∈ s, p i * Real.log (p i)) * total := by
      calc
        ∑ i ∈ s, x i * Real.log (x i) =
            (∑ i ∈ s, total * p i * Real.log total) +
              (∑ i ∈ s, total * p i * Real.log (p i)) := hrewrite
        _ =
            (∑ i ∈ s, p i) * (total * Real.log total) +
              (∑ i ∈ s, p i * Real.log (p i)) * total := by
            simp [hfirst, hsecond]
    have hsplit :
        ∑ i ∈ s, x i * Real.log (x i) =
          total * Real.log total +
            total * ∑ i ∈ s, p i * Real.log (p i) := by
      have hmove :
          (∑ i ∈ s, p i * Real.log (p i)) * total =
            total * ∑ i ∈ s, p i * Real.log (p i) := by
        simp [mul_comm]
      have hmove' :
          (∑ i ∈ s, p i) * (total * Real.log total) =
            total * Real.log total := by
        simp [hp_sum]
      have := hsplit_main
      simpa [hmove, hmove'] using this
    have hprob_le :
        ∑ i ∈ s, p i * Real.log (p i) ≤ 0 :=
      sum_prob_log_le_zero s p hp_nonneg hp_sum
    have hmul_le :
        total * ∑ i ∈ s, p i * Real.log (p i) ≤ 0 := by
      have :=
        mul_le_mul_of_nonneg_left hprob_le htotal_pos.le
      simpa [zero_mul] using this
    have := add_le_add_left hmul_le (total * Real.log total)
    simpa [hsplit, total] using this

lemma logSum_inequality {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ)
    (ha_pos : ∀ i ∈ s, 0 < a i) (hb_pos : ∀ i ∈ s, 0 < b i)
    (ha_sum_pos : 0 < ∑ i ∈ s, a i) (hb_sum_pos : 0 < ∑ i ∈ s, b i) :
    ∑ i ∈ s, a i * (Real.log (a i) - Real.log (b i)) ≥
      (∑ i ∈ s, a i) *
        (Real.log (∑ i ∈ s, a i) - Real.log (∑ i ∈ s, b i)) := by
  classical
  set totalA := ∑ i ∈ s, a i
  set totalB := ∑ i ∈ s, b i
  have htotalA_pos : 0 < totalA := ha_sum_pos
  have htotalB_pos : 0 < totalB := hb_sum_pos
  have htotalA_ne : (totalA : ℝ) ≠ 0 := htotalA_pos.ne'
  have htotalB_ne : (totalB : ℝ) ≠ 0 := htotalB_pos.ne'
  set w : ι → ℝ := fun i => b i / totalB
  set x : ι → ℝ := fun i => a i / b i
  have hw_nonneg :
      ∀ i ∈ s, 0 ≤ w i := fun i hi =>
    div_nonneg (le_of_lt (hb_pos i hi)) htotalB_pos.le
  have hw_sum :
      ∑ i ∈ s, w i = 1 := by
    have hsum :
        (∑ i ∈ s, b i / totalB) = (∑ i ∈ s, b i) / totalB :=
      (Finset.sum_div (s := s) (f := fun i => b i) totalB).symm
    have htotal :
        (∑ i ∈ s, b i) / totalB = 1 := by
      simp [totalB, htotalB_ne]
    simpa [w] using hsum.trans htotal
  have hx_nonneg :
      ∀ i ∈ s, 0 ≤ x i := fun i hi =>
    div_nonneg (le_of_lt (ha_pos i hi)) (le_of_lt (hb_pos i hi))
  have hb_ne : ∀ i ∈ s, (b i) ≠ 0 := fun i hi => (hb_pos i hi).ne'
  have ha_ne : ∀ i ∈ s, (a i) ≠ 0 := fun i hi => (ha_pos i hi).ne'
  have hstep :
      ∀ i ∈ s, w i * x i = a i / totalB := by
    intro i hi
    have hb' : (b i) ≠ 0 := hb_ne i hi
    have hmul :
        (b i / totalB) * (a i / b i) = a i / totalB := by
      field_simp [hb', htotalB_ne]
    simpa [w, x] using hmul
  have hsum_wx :
      ∑ i ∈ s, w i * x i = totalA / totalB := by
    calc
      ∑ i ∈ s, w i * x i
          = ∑ i ∈ s, a i / totalB := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hstep i hi]
      _ = (∑ i ∈ s, a i) / totalB :=
        (Finset.sum_div (s := s) (f := fun i => a i) totalB).symm
      _ = totalA / totalB := by simp [totalA]
  have hsum_scaled :
      totalB * ∑ i ∈ s, w i * (x i * Real.log (x i)) =
        ∑ i ∈ s, a i * Real.log (a i / b i) := by
    have hterm :
        ∀ i ∈ s, totalB * (w i * (x i * Real.log (x i))) =
          a i * Real.log (a i / b i) := by
      intro i hi
      have hwx : w i * x i = a i / totalB := hstep i hi
      have hxlog : Real.log (x i) = Real.log (a i / b i) := by
        simp [x]
      calc
        totalB * (w i * (x i * Real.log (x i)))
            = totalB * ((w i * x i) * Real.log (x i)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        _ = totalB * ((a i / totalB) * Real.log (x i)) := by
              simp [hwx]
        _ = (totalB * (a i / totalB)) * Real.log (x i) := by
              simp [mul_assoc]
        _ = a i * Real.log (x i) := by
              field_simp [htotalB_ne]
        _ = a i * Real.log (a i / b i) := by
              simp [hxlog]
    calc
      totalB * ∑ i ∈ s, w i * (x i * Real.log (x i))
          = ∑ i ∈ s, totalB * (w i * (x i * Real.log (x i))) := by
              simp [Finset.mul_sum]
      _ = ∑ i ∈ s, a i * Real.log (a i / b i) := by
              refine Finset.sum_congr rfl ?_; intro i hi; simpa using hterm i hi
  have hineq :=
    convexCombo_mul_log_le (s := s) (w := w) (x := x)
      hw_nonneg hw_sum hx_nonneg
  have hineq' :
      totalA * Real.log (totalA / totalB) ≤
        ∑ i ∈ s, a i * Real.log (a i / b i) := by
    have htmp :=
      mul_le_mul_of_nonneg_left
        (by simpa [hsum_wx] using hineq) htotalB_pos.le
    have hleft :
        totalB * ((totalA / totalB) * Real.log (totalA / totalB)) =
          totalA * Real.log (totalA / totalB) := by
      field_simp [htotalB_ne, mul_comm, mul_left_comm, mul_assoc]
    simpa [hsum_wx, hsum_scaled, hleft] using htmp
  have hleft :
      ∑ i ∈ s, a i * (Real.log (a i) - Real.log (b i)) =
        ∑ i ∈ s, a i * Real.log (a i / b i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have ha' : (a i) ≠ 0 := ha_ne i hi
    have hb' : (b i) ≠ 0 := hb_ne i hi
    simp [Real.log_div ha' hb']
  have hright :
      (∑ i ∈ s, a i) *
          (Real.log (∑ i ∈ s, a i) - Real.log (∑ i ∈ s, b i)) =
        totalA * Real.log (totalA / totalB) := by
    simp [totalA, totalB, Real.log_div htotalA_ne htotalB_ne]
  simpa [hleft, ← hright] using hineq'

end ActiveInference
end Quantum
end HeytingLean
