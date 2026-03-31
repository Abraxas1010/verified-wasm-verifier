import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Epiplexity.Info
import HeytingLean.Epiplexity.Prelude
import HeytingLean.Probability.InfoTheory.KL

namespace HeytingLean
namespace Epiplexity
namespace Crypto

open scoped BigOperators

noncomputable section

open HeytingLean.Probability
open HeytingLean.Probability.InfoTheory
open HeytingLean.Epiplexity.Info

namespace BitStr

instance (n : Nat) : Nonempty (BitStr n) := by
  refine ⟨⟨0, ?_⟩⟩
  exact Nat.pow_pos (a := 2) (n := n) (Nat.succ_pos 1)

end BitStr

namespace FinDist

/-- Probability mass of a decidable event under a finite distribution. -/
noncomputable def probEvent {α : Type u} [Fintype α] (P : FinDist α) (E : α → Prop)
    [DecidablePred E] : ℝ :=
  ∑ a : α, if E a then P.pmf a else 0

theorem probEvent_add_probEvent_not {α : Type u} [Fintype α] (P : FinDist α) (E : α → Prop)
    [DecidablePred E] :
    probEvent P E + probEvent P (fun a => ¬E a) = 1 := by
  classical
  unfold probEvent
  have hpoint : ∀ a : α,
      (if E a then P.pmf a else 0) + (if ¬E a then P.pmf a else 0) = P.pmf a := by
    intro a
    by_cases h : E a <;> simp [h]
  calc
    (∑ a : α, if E a then P.pmf a else 0) + (∑ a : α, if ¬E a then P.pmf a else 0)
        = ∑ a : α, ((if E a then P.pmf a else 0) + (if ¬E a then P.pmf a else 0)) := by
            simp [Finset.sum_add_distrib]
    _ = ∑ a : α, P.pmf a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          exact hpoint a
    _ = 1 := by
          exact P.sum_one

theorem probEvent_mono {α : Type u} [Fintype α] (P : FinDist α) {E F : α → Prop}
    [DecidablePred E] [DecidablePred F] (hEF : ∀ a, E a → F a) :
    probEvent P E ≤ probEvent P F := by
  classical
  unfold probEvent
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases hE : E a
  · have hF : F a := hEF a hE
    simp [hE, hF]
  · by_cases hF : F a
    · simp [hE, hF, P.nonneg a]
    · simp [hE, hF]

/-- Finite Markov inequality for `FinDist` in `ℝ`. -/
theorem markov {α : Type u} [Fintype α] (P : FinDist α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    {c : ℝ} (hc : 0 < c) :
    probEvent P (fun a => c ≤ f a) ≤ (∑ a : α, P.pmf a * f a) / c := by
  classical
  -- Pointwise: on `{c ≤ f a}`, we have `c ≤ f a`; otherwise the indicator is `0`.
  have hpoint : ∀ a : α,
      (if c ≤ f a then P.pmf a else 0) * c ≤ P.pmf a * f a := by
    intro a
    by_cases h : c ≤ f a
    · have hmul : P.pmf a * c ≤ P.pmf a * f a :=
        mul_le_mul_of_nonneg_left h (P.nonneg a)
      simpa [h, mul_assoc] using hmul
    · have hrhs : 0 ≤ P.pmf a * f a := mul_nonneg (P.nonneg a) (hf a)
      simp [h, hrhs]
  have hsum :
      (∑ a : α, (if c ≤ f a then P.pmf a else 0) * c) ≤ ∑ a : α, P.pmf a * f a := by
    refine Finset.sum_le_sum ?_
    intro a _
    exact hpoint a
  have hleft :
      probEvent P (fun a => c ≤ f a) * c =
        ∑ a : α, (if c ≤ f a then P.pmf a else 0) * c := by
    unfold probEvent
    simp [Finset.sum_mul]
  have hmul : probEvent P (fun a => c ≤ f a) * c ≤ ∑ a : α, P.pmf a * f a := by
    calc
      probEvent P (fun a => c ≤ f a) * c
          = ∑ a : α, (if c ≤ f a then P.pmf a else 0) * c := hleft
      _ ≤ ∑ a : α, P.pmf a * f a := hsum
  exact (le_div_iff₀ hc).2 hmul

end FinDist

/-- Threshold `2^{-2(m+t)}` (paper Definition 21), expressed as a real number. -/
noncomputable def heavyThreshold (m t : Nat) : ℝ :=
  (1 : ℝ) / ((2 : ℝ) ^ (2 * (m + t)))

/-- Heavy set `A_{Q,t} := {z | Q z ≥ 2^{-2(m+t)}}` as a finite set. -/
noncomputable def heavySet {α : Type u} [Fintype α] (Q : FinDist α) (m t : Nat) : Finset α := by
  classical
  exact Finset.univ.filter (fun z : α => heavyThreshold m t ≤ Q.pmf z)

namespace HeavySet

open FinDist

variable {α : Type u} [Fintype α]

theorem mem_heavySet_iff (Q : FinDist α) (m t : Nat) (z : α) :
    z ∈ heavySet (α := α) Q m t ↔ heavyThreshold m t ≤ Q.pmf z := by
  classical
  simp [heavySet]

theorem prob_heavySet {P Q : FinDist α} (m t : Nat) :
    (heavySet (α := α) Q m t).sum (fun z => P.pmf z)
      = probEvent P (fun z => heavyThreshold m t ≤ Q.pmf z) := by
  classical
  unfold probEvent
  -- The event probability is the sum over the filtered univ.
  simp [heavySet, Finset.sum_filter]

theorem log_threshold (m t : Nat) :
    Real.log (heavyThreshold m t) = -((2 * (m + t) : Nat) : ℝ) * Real.log 2 := by
  -- `log(1 / 2^k) = -log(2^k) = -(k*log 2)`.
  simp [heavyThreshold, one_div, Real.log_inv, Real.log_pow]

theorem nllBits_ge_of_not_heavy (Q : FinDist α) (hq : Q.Pos) (m t : Nat) (z : α)
    (hz : ¬heavyThreshold m t ≤ Q.pmf z) :
    ((2 * (m + t) : Nat) : ℝ) ≤ Info.nllBits Q z := by
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hqz_pos : 0 < Q.pmf z := hq z
  have hz_lt : Q.pmf z < heavyThreshold m t := lt_of_not_ge hz
  have hlog_lt : Real.log (Q.pmf z) < Real.log (heavyThreshold m t) :=
    Real.log_lt_log hqz_pos hz_lt
  have hlog_thr : Real.log (heavyThreshold m t) = -((2 * (m + t) : Nat) : ℝ) * Real.log 2 :=
    log_threshold (m := m) (t := t)
  -- Convert to `-log(q)/log 2 ≥ k`.
  have hneg : -Real.log (Q.pmf z) > ((2 * (m + t) : Nat) : ℝ) * Real.log 2 := by
    -- From `log q < -k*log2`, negate.
    linarith [hlog_lt, hlog_thr]
  -- Rewrite `nllBits` as `(-log q)/log 2`.
  unfold Info.nllBits Info.nllNat
  have hsafelog : InfoTheory.safeLog (Q.pmf z) = Real.log (Q.pmf z) :=
    InfoTheory.safeLog_of_pos hqz_pos
  have : ((2 * (m + t) : Nat) : ℝ) * Real.log 2 / Real.log 2 ≤ (-Real.log (Q.pmf z)) / Real.log 2 := by
    have : ((2 * (m + t) : Nat) : ℝ) * Real.log 2 ≤ -Real.log (Q.pmf z) := by
      linarith [hneg]
    exact (div_le_div_of_nonneg_right this (le_of_lt hlog2_pos))
  have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
  -- Simplify `k*log2/log2 = k`.
  simpa [hsafelog, hlog2_ne0] using this

theorem crossEntropyNat_eq_entropy_add_klDiv (P Q : FinDist α) :
    Info.crossEntropyNat P Q = FinDist.entropy P + FinDist.klDiv P Q := by
  classical
  -- This identity holds *without* assuming `P.Pos`, because our definitions use `safeLog`
  -- and define the `p=0` contributions as `0`.
  unfold Info.crossEntropyNat Info.nllNat FinDist.entropy FinDist.klDiv
  have hterm :
      ∀ a : α,
        P.pmf a * (-InfoTheory.safeLog (Q.pmf a)) =
          InfoTheory.entropyTerm (P.pmf a) + InfoTheory.klTerm (P.pmf a) (Q.pmf a) := by
    intro a
    by_cases hp : P.pmf a ≤ 0
    · have hp0 : P.pmf a = 0 := le_antisymm hp (P.nonneg a)
      -- `P.pmf a` is an application, so rewrite rather than `subst`.
      simp [hp0, InfoTheory.entropyTerm, InfoTheory.klTerm]
    · have hp_not_le : ¬P.pmf a ≤ 0 := hp
      simp [InfoTheory.entropyTerm, InfoTheory.klTerm, hp_not_le, sub_eq_add_neg]
      ring
  calc
    (∑ a : α, P.pmf a * (-InfoTheory.safeLog (Q.pmf a)))
        = ∑ a : α, (InfoTheory.entropyTerm (P.pmf a) + InfoTheory.klTerm (P.pmf a) (Q.pmf a)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact hterm a
    _ = (∑ a : α, InfoTheory.entropyTerm (P.pmf a)) + (∑ a : α, InfoTheory.klTerm (P.pmf a) (Q.pmf a)) := by
          simp [Finset.sum_add_distrib]

theorem crossEntropyBits_eq_entropyBits_add_klBits (P Q : FinDist α) :
    Info.crossEntropyBits P Q =
      Info.entropyBits P + (FinDist.klDiv P Q) / Real.log 2 := by
  classical
  have hceNat :
      Info.crossEntropyNat P Q = FinDist.entropy P + FinDist.klDiv P Q :=
    crossEntropyNat_eq_entropy_add_klDiv (P := P) (Q := Q)
  have hbits : Info.crossEntropyBits P Q = Info.crossEntropyNat P Q / Real.log 2 :=
    Info.crossEntropyBits_eq_crossEntropyNat_div_log2 (p := P) (q := Q)
  unfold Info.entropyBits
  calc
    Info.crossEntropyBits P Q = Info.crossEntropyNat P Q / Real.log 2 := hbits
    _ = (FinDist.entropy P + FinDist.klDiv P Q) / Real.log 2 := by
          simp [hceNat]
    _ = FinDist.entropy P / Real.log 2 + FinDist.klDiv P Q / Real.log 2 := by ring
    _ = Info.entropyBits P + FinDist.klDiv P Q / Real.log 2 := by rfl

/-- Lemma 22 (paper): heavy-set probability bound via Markov inequality. -/
theorem lemma22_prob_heavySet_ge_half (P Q : FinDist α) (hq : Q.Pos) (m t : Nat)
    (hH : Info.entropyBits P = m)
    (hKL : (FinDist.klDiv P Q) / Real.log 2 ≤ t)
    (hmt : 0 < m + t) :
    probEvent P (fun z => heavyThreshold m t ≤ Q.pmf z) ≥ (1 / 2 : ℝ) := by
  classical
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hce :
      Info.crossEntropyBits P Q ≤ (m : ℝ) + (t : ℝ) := by
    have hbits : Info.crossEntropyBits P Q =
        Info.entropyBits P + (FinDist.klDiv P Q) / Real.log 2 :=
      crossEntropyBits_eq_entropyBits_add_klBits (P := P) (Q := Q)
    calc
      Info.crossEntropyBits P Q
          = Info.entropyBits P + (FinDist.klDiv P Q) / Real.log 2 := hbits
      _ ≤ (m : ℝ) + (t : ℝ) := by
            have hent : Info.entropyBits P ≤ (m : ℝ) := by simp [hH]
            have : Info.entropyBits P + (FinDist.klDiv P Q) / Real.log 2 ≤
                (m : ℝ) + (t : ℝ) := by
                  gcongr
            simpa using this
  -- Markov bound on the "not heavy" event, via `nllBits`.
  let kNat : Nat := 2 * (m + t)
  let k : ℝ := (kNat : ℝ)
  have hnll_nonneg : ∀ z : α, 0 ≤ Info.nllBits Q z := by
    intro z
    exact Info.nllBits_nonneg (q := Q) hq z
  have hmt_posR : 0 < ((m : ℝ) + (t : ℝ)) := by
    have : 0 < ((m + t : Nat) : ℝ) := by exact_mod_cast hmt
    simpa [Nat.cast_add] using this
  have hmt_ne0R : ((m : ℝ) + (t : ℝ)) ≠ 0 := ne_of_gt hmt_posR
  have hk_def : k = (2 : ℝ) * ((m : ℝ) + (t : ℝ)) := by
    simp [k, kNat, Nat.cast_mul, Nat.cast_add]
  have hk_pos : 0 < k := by
    have : 0 < (2 : ℝ) * ((m : ℝ) + (t : ℝ)) := mul_pos (by norm_num) hmt_posR
    simpa [hk_def] using this
  have hmarkov :
      probEvent P (fun z => (k : ℝ) ≤ Info.nllBits Q z)
        ≤ (∑ z : α, P.pmf z * Info.nllBits Q z) / k :=
    FinDist.markov (P := P) (f := fun z => Info.nllBits Q z) hnll_nonneg (c := k) hk_pos
  have hmarkov' :
      probEvent P (fun z => (k : ℝ) ≤ Info.nllBits Q z) ≤ (Info.crossEntropyBits P Q) / k := by
    simpa [Info.crossEntropyBits] using hmarkov
  have hk_ratio : ((m : ℝ) + (t : ℝ)) / k = (1 / 2 : ℝ) := by
    calc
      ((m : ℝ) + (t : ℝ)) / k
          = ((m : ℝ) + (t : ℝ)) / ((2 : ℝ) * ((m : ℝ) + (t : ℝ))) := by simp [hk_def]
      _ = (1 / 2 : ℝ) := by
            field_simp [hmt_ne0R]
  have hk_lower : (Info.crossEntropyBits P Q) / k ≤ (1 / 2 : ℝ) := by
    have hdiv : (Info.crossEntropyBits P Q) / k ≤ ((m : ℝ) + (t : ℝ)) / k :=
      div_le_div_of_nonneg_right hce (le_of_lt hk_pos)
    exact le_trans hdiv (by simp [hk_ratio])
  have hnot_heavy_le :
      probEvent P (fun z => ¬heavyThreshold m t ≤ Q.pmf z) ≤ (1 / 2 : ℝ) := by
    have hsub : ∀ z, (¬heavyThreshold m t ≤ Q.pmf z) → (k : ℝ) ≤ Info.nllBits Q z := by
      intro z hz
      have := nllBits_ge_of_not_heavy (Q := Q) hq (m := m) (t := t) z hz
      simpa [k, kNat] using this
    have hmono :
        probEvent P (fun z => ¬heavyThreshold m t ≤ Q.pmf z)
          ≤ probEvent P (fun z => (k : ℝ) ≤ Info.nllBits Q z) :=
      probEvent_mono (P := P) (E := fun z => ¬heavyThreshold m t ≤ Q.pmf z)
        (F := fun z => (k : ℝ) ≤ Info.nllBits Q z) hsub
    have : probEvent P (fun z => (k : ℝ) ≤ Info.nllBits Q z) ≤ (1 / 2 : ℝ) :=
      le_trans hmarkov' hk_lower
    exact le_trans hmono this
  have hadd :
      probEvent P (fun z => heavyThreshold m t ≤ Q.pmf z) +
          probEvent P (fun z => ¬heavyThreshold m t ≤ Q.pmf z) = 1 :=
    probEvent_add_probEvent_not (P := P) (E := fun z => heavyThreshold m t ≤ Q.pmf z)
  have : (1 / 2 : ℝ) ≤ probEvent P (fun z => heavyThreshold m t ≤ Q.pmf z) := by
    have : probEvent P (fun z => ¬heavyThreshold m t ≤ Q.pmf z) ≤ (1 / 2 : ℝ) := hnot_heavy_le
    linarith [hadd, this]
  linarith

/-- Lemma 23 (paper): heavy-set weight under the uniform distribution. -/
theorem lemma23_prob_uniform_heavySet_le_general {γ : Type u} [Fintype γ] [Nonempty γ]
    (m t : Nat) (Q : FinDist γ) :
    let U : FinDist γ := Epiplexity.FinDist.uniform (α := γ)
    (heavySet (α := γ) Q m t).sum (fun z => U.pmf z) ≤
      ((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card γ : ℝ) := by
  classical
  intro U
  -- Cardinality bound: `|A| ≤ 2^{2(m+t)}` since `∑_{z∈A} Q(z) ≤ 1` and each term is ≥ threshold.
  let A : Finset γ := heavySet (α := γ) Q m t
  have hthr_pos : 0 < heavyThreshold m t := by
    simp [heavyThreshold, one_div]
  have hcard :
      (A.card : ℝ) ≤ (2 : ℝ) ^ (2 * (m + t)) := by
    -- `A.card * threshold ≤ ∑_{z∈A} Q(z) ≤ 1`.
    have hA_sum :
        (A.card : ℝ) * heavyThreshold m t ≤ A.sum (fun z => Q.pmf z) := by
      -- each term contributes at least `threshold`.
      have hterm : ∀ z, z ∈ A → heavyThreshold m t ≤ Q.pmf z := by
        intro z hz
        exact (mem_heavySet_iff (α := γ) (Q := Q) (m := m) (t := t) z).1 hz
      -- sum of lower bounds
      have : (A.card : ℝ) * heavyThreshold m t = A.sum (fun _ => heavyThreshold m t) := by
        simp [Finset.sum_const]
      -- compare sums termwise
      have hsum : A.sum (fun _ => heavyThreshold m t) ≤ A.sum (fun z => Q.pmf z) := by
        refine Finset.sum_le_sum ?_
        intro z hz
        exact hterm z hz
      exact le_trans (le_of_eq this) hsum
    have hsum_le_one : A.sum (fun z => Q.pmf z) ≤ 1 := by
      have hsub : A ⊆ Finset.univ := by intro z hz; exact Finset.mem_univ z
      have hnonneg : ∀ z, 0 ≤ Q.pmf z := Q.nonneg
      have hle : A.sum (fun z => Q.pmf z) ≤ (Finset.univ.sum fun z : γ => Q.pmf z) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro z _ _; exact hnonneg z)
      exact le_trans hle (le_of_eq Q.sum_one)
    have hA : (A.card : ℝ) * heavyThreshold m t ≤ 1 := le_trans hA_sum hsum_le_one
    -- divide by `threshold > 0`
    have : (A.card : ℝ) ≤ 1 / heavyThreshold m t := by
      exact (le_div_iff₀ hthr_pos).2 hA
    -- `1 / (1 / 2^k) = 2^k`.
    simpa [heavyThreshold] using this
  -- Uniform probability is `|A| / |γ|`.
  have hpmf : ∀ z : γ, U.pmf z = 1 / (Fintype.card γ : ℝ) := by
    intro z
    simp [U]
  calc
    A.sum (fun z => U.pmf z)
        = (A.card : ℝ) * (1 / (Fintype.card γ : ℝ)) := by
            simp [hpmf, Finset.sum_const]
    _ ≤ ((2 : ℝ) ^ (2 * (m + t))) * (1 / (Fintype.card γ : ℝ)) := by
          gcongr
    _ = ((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card γ : ℝ) := by
          simp [div_eq_mul_inv]

/-- Lemma 23 (paper): heavy-set weight under the uniform distribution. -/
theorem lemma23_prob_uniform_heavySet_le (n m t : Nat) (Q : FinDist (BitStr n)) :
    let U : FinDist (BitStr n) := Epiplexity.FinDist.uniform (α := BitStr n)
    (heavySet (α := BitStr n) Q m t).sum (fun z => U.pmf z) ≤
      ((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr n) : ℝ) := by
  classical
  intro U
  -- Cardinality bound: `|A| ≤ 2^{2(m+t)}` since `∑_{z∈A} Q(z) ≤ 1` and each term is ≥ threshold.
  let A : Finset (BitStr n) := heavySet (α := BitStr n) Q m t
  have hthr_pos : 0 < heavyThreshold m t := by
    simp [heavyThreshold, one_div]
  have hcard :
      (A.card : ℝ) ≤ (2 : ℝ) ^ (2 * (m + t)) := by
    -- `A.card * threshold ≤ ∑_{z∈A} Q(z) ≤ 1`.
    have hA_sum :
        (A.card : ℝ) * heavyThreshold m t ≤ A.sum (fun z => Q.pmf z) := by
      -- each term contributes at least `threshold`.
      have hterm : ∀ z, z ∈ A → heavyThreshold m t ≤ Q.pmf z := by
        intro z hz
        exact (mem_heavySet_iff (α := BitStr n) (Q := Q) (m := m) (t := t) z).1 hz
      -- sum of lower bounds
      have : (A.card : ℝ) * heavyThreshold m t = A.sum (fun _ => heavyThreshold m t) := by
        simp [Finset.sum_const]
      -- compare sums termwise
      have hsum : A.sum (fun _ => heavyThreshold m t) ≤ A.sum (fun z => Q.pmf z) := by
        refine Finset.sum_le_sum ?_
        intro z hz
        exact hterm z hz
      exact le_trans (le_of_eq this) hsum
    have hsum_le_one : A.sum (fun z => Q.pmf z) ≤ 1 := by
      have hsub : A ⊆ Finset.univ := by intro z hz; exact Finset.mem_univ z
      have hnonneg : ∀ z, 0 ≤ Q.pmf z := Q.nonneg
      have hle : A.sum (fun z => Q.pmf z) ≤ (Finset.univ.sum fun z : BitStr n => Q.pmf z) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro z _ _; exact hnonneg z)
      exact le_trans hle (le_of_eq Q.sum_one)
    have hA : (A.card : ℝ) * heavyThreshold m t ≤ 1 := le_trans hA_sum hsum_le_one
    -- divide by `threshold > 0`
    have : (A.card : ℝ) ≤ 1 / heavyThreshold m t := by
      exact (le_div_iff₀ hthr_pos).2 hA
    -- `1 / (1 / 2^k) = 2^k`.
    simpa [heavyThreshold] using this
  -- Uniform probability is `|A| / |BitStr n|`.
  have hpmf : ∀ z : BitStr n, U.pmf z = 1 / (Fintype.card (BitStr n) : ℝ) := by
    intro z
    simp [U]
  calc
    A.sum (fun z => U.pmf z)
        = (A.card : ℝ) * (1 / (Fintype.card (BitStr n) : ℝ)) := by
            simp [hpmf, Finset.sum_const]
    _ ≤ ((2 : ℝ) ^ (2 * (m + t))) * (1 / (Fintype.card (BitStr n) : ℝ)) := by
          gcongr
    _ = ((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr n) : ℝ) := by
          simp [div_eq_mul_inv]

end HeavySet

end

end Crypto
end Epiplexity
end HeytingLean
