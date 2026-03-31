import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import HeytingLean.Epiplexity.Prelude
import HeytingLean.Probability.InfoTheory

namespace HeytingLean
namespace Epiplexity

open scoped BigOperators

open HeytingLean.Probability

noncomputable section

namespace Info

open HeytingLean.Probability.InfoTheory

variable {α : Type u} [Fintype α]

/-- Any mass in a `FinDist` is at most `1` since the total mass is `1`. -/
theorem pmf_le_one (p : InfoTheory.FinDist α) (a : α) : p.pmf a ≤ 1 := by
  classical
  have hle : p.pmf a ≤ ∑ b : α, p.pmf b := by
    simpa using
      (Finset.single_le_sum (fun b _ => p.nonneg b) (by simp))
  simpa [p.sum_one] using hle

/-- Negative log-likelihood in nats (totalized via `safeLog`). -/
def nllNat (q : InfoTheory.FinDist α) (a : α) : ℝ :=
  -InfoTheory.safeLog (q.pmf a)

/-- Negative log-likelihood in bits (base-2). -/
def nllBits (q : InfoTheory.FinDist α) (a : α) : ℝ :=
  nllNat q a / Real.log 2

theorem nllBits_nonneg (q : InfoTheory.FinDist α) (hq : q.Pos) (a : α) : 0 ≤ nllBits q a := by
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hq_le_one : q.pmf a ≤ 1 := pmf_le_one (p := q) a
  have hlogq_nonpos : Real.log (q.pmf a) ≤ 0 :=
    Real.log_nonpos (q.nonneg a) hq_le_one
  have hsafelog : InfoTheory.safeLog (q.pmf a) = Real.log (q.pmf a) :=
    InfoTheory.safeLog_of_pos (hq a)
  unfold nllBits nllNat
  have : 0 ≤ -Real.log (q.pmf a) := by linarith
  have : 0 ≤ (-Real.log (q.pmf a)) / Real.log 2 :=
    div_nonneg this (le_of_lt hlog2_pos)
  simpa [hsafelog] using this

/-- Cross-entropy `E_p[-log q]` in nats. -/
def crossEntropyNat (p q : InfoTheory.FinDist α) : ℝ :=
  ∑ a : α, p.pmf a * nllNat q a

/-- Cross-entropy `E_p[-log₂ q]` in bits. -/
def crossEntropyBits (p q : InfoTheory.FinDist α) : ℝ :=
  ∑ a : α, p.pmf a * nllBits q a

theorem crossEntropyBits_eq_crossEntropyNat_div_log2 (p q : InfoTheory.FinDist α) :
    crossEntropyBits p q = crossEntropyNat p q / Real.log 2 := by
  classical
  unfold crossEntropyBits crossEntropyNat nllBits
  -- Pull out the constant factor `(Real.log 2)⁻¹`.
  simp [div_eq_mul_inv, mul_assoc, Finset.sum_mul]

/-- Cross-entropy is nonnegative under `q.Pos`. -/
theorem crossEntropyBits_nonneg (p q : InfoTheory.FinDist α) (hq : q.Pos) :
    0 ≤ crossEntropyBits p q := by
  classical
  unfold crossEntropyBits
  have hterm_nonneg : ∀ a : α, 0 ≤ p.pmf a * nllBits q a := by
    intro a
    exact mul_nonneg (p.nonneg a) (nllBits_nonneg (q := q) hq a)
  have hsum_nonneg : 0 ≤ ∑ a : α, p.pmf a * nllBits q a :=
    Finset.sum_nonneg (fun a _ => hterm_nonneg a)
  exact hsum_nonneg

/-- Shannon entropy in bits, derived from the existing nat-based `FinDist.entropy`. -/
def entropyBits (p : InfoTheory.FinDist α) : ℝ :=
  InfoTheory.FinDist.entropy p / Real.log 2

theorem crossEntropyNat_eq_neg_sum_mul_log_of_Pos
    (p q : InfoTheory.FinDist α) (hq : q.Pos) :
    crossEntropyNat p q = -∑ a : α, p.pmf a * Real.log (q.pmf a) := by
  classical
  unfold crossEntropyNat nllNat
  have hlog : ∀ a : α, InfoTheory.safeLog (q.pmf a) = Real.log (q.pmf a) := by
    intro a
    exact InfoTheory.safeLog_of_pos (hq a)
  -- Push the `safeLog` rewrite through the sum, then pull out the minus sign.
  calc
    (∑ a : α, p.pmf a * (-InfoTheory.safeLog (q.pmf a)))
        = ∑ a : α, p.pmf a * (-Real.log (q.pmf a)) := by
            simp [hlog]
    _ = ∑ a : α, -(p.pmf a * Real.log (q.pmf a)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          ring
    _ = -∑ a : α, p.pmf a * Real.log (q.pmf a) := by
          simp

theorem crossEntropyNat_eq_entropy_add_klDiv
    (p q : InfoTheory.FinDist α) (hp : p.Pos) (hq : q.Pos) :
    crossEntropyNat p q = InfoTheory.FinDist.entropy p + InfoTheory.FinDist.klDiv p q := by
  classical
  set A : ℝ := ∑ a : α, p.pmf a * Real.log (p.pmf a)
  set B : ℝ := ∑ a : α, p.pmf a * Real.log (q.pmf a)
  have hent : InfoTheory.FinDist.entropy p = -A := by
    simpa [A] using InfoTheory.FinDist.entropy_eq_neg_sum_mul_log_of_Pos p hp
  have hce : crossEntropyNat p q = -B := by
    simpa [B] using crossEntropyNat_eq_neg_sum_mul_log_of_Pos (p := p) (q := q) hq
  have hkl : InfoTheory.FinDist.klDiv p q = A - B := by
    have hkl0 :
        InfoTheory.FinDist.klDiv p q
          = ∑ a : α, p.pmf a * (Real.log (p.pmf a) - Real.log (q.pmf a)) :=
      InfoTheory.FinDist.klDiv_eq_sum_mul_log_sub_of_Pos p q hp hq
    have hsum :
        (∑ a : α, p.pmf a * (Real.log (p.pmf a) - Real.log (q.pmf a))) = A - B := by
      simp [A, B, mul_sub, Finset.sum_sub_distrib]
    simpa [hsum] using hkl0
  calc
    crossEntropyNat p q = -B := hce
    _ = (-A) + (A - B) := by ring
    _ = InfoTheory.FinDist.entropy p + InfoTheory.FinDist.klDiv p q := by
          simp [hent, hkl]

theorem crossEntropyBits_ge_entropyBits
    (p q : InfoTheory.FinDist α) (hp : p.Pos) (hq : q.Pos) :
    entropyBits p ≤ crossEntropyBits p q := by
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hce : crossEntropyNat p q = InfoTheory.FinDist.entropy p + InfoTheory.FinDist.klDiv p q :=
    crossEntropyNat_eq_entropy_add_klDiv (p := p) (q := q) hp hq
  have hkl_nonneg : 0 ≤ InfoTheory.FinDist.klDiv p q :=
    InfoTheory.FinDist.klDiv_nonneg_of_Pos p q hq
  have hbits : crossEntropyBits p q = crossEntropyNat p q / Real.log 2 :=
    crossEntropyBits_eq_crossEntropyNat_div_log2 (p := p) (q := q)
  unfold entropyBits
  -- Divide the nat-level inequality by `log 2 > 0`.
  have hent_le : InfoTheory.FinDist.entropy p ≤ crossEntropyNat p q := by
    have : InfoTheory.FinDist.entropy p ≤ InfoTheory.FinDist.entropy p + InfoTheory.FinDist.klDiv p q :=
      le_add_of_nonneg_right hkl_nonneg
    simpa [hce] using this
  have hdiv :
      InfoTheory.FinDist.entropy p / Real.log 2 ≤ crossEntropyNat p q / Real.log 2 :=
    div_le_div_of_nonneg_right hent_le (le_of_lt hlog2_pos)
  simpa [hbits] using hdiv

end Info

end

end Epiplexity
end HeytingLean
