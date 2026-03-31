import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Epiplexity.Bounds
import HeytingLean.Epiplexity.Crypto.Axioms
import HeytingLean.Epiplexity.Crypto.HeavySet

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

open FinDist

namespace CSPRNG

/-!
CSPRNG results (paper Appendix A.1–A.3): Theorems 17/19 plus main-text bundles (Theorems 9/12/18).

We keep the probability spaces finite (`BitStr n`) and treat cryptographic security hypotheses as
explicit Props (`CSPRNGSecure` from `Crypto.Axioms`).
-/

noncomputable def Un (n : Nat) : FinDist (BitStr n) :=
  Epiplexity.FinDist.uniform (α := BitStr n)

/-- The PRG output distribution `G(U_k)`. -/
noncomputable def prgDist {k n : Nat} (G : BitStr k → BitStr n) : FinDist (BitStr n) :=
  FinDist.map G (Epiplexity.FinDist.uniform (α := BitStr k))

/-! ### Small algebraic helpers -/

/-- Indicator (as a real `0/1`) for a threshold event on a real. -/
noncomputable def ind (z : ℝ) (u : Nat) : ℝ :=
  if z ≤ (u : ℝ) then 1 else 0

theorem ind_nonneg (z : ℝ) (u : Nat) : 0 ≤ ind z u := by
  by_cases h : z ≤ (u : ℝ) <;> simp [ind, h]

/-- A discrete “layercake” inequality: `n - z` is controlled by how often `z ≤ u` for `u < n`. -/
theorem layercake_pointwise (n : Nat) (z : ℝ) (hz0 : 0 ≤ z) :
    (n : ℝ) - z ≤ (1 : ℝ) + (∑ u ∈ Finset.range n, ind z u) := by
  classical
  let m : Nat := Nat.ceil z
  by_cases hnz : (n : ℝ) ≤ z
  · have hL : (n : ℝ) - z ≤ 0 := by linarith
    have hsum_nonneg : 0 ≤ (∑ u ∈ Finset.range n, ind z u) := by
      refine Finset.sum_nonneg ?_
      intro u hu
      exact ind_nonneg z u
    linarith
  · have hnz' : z < (n : ℝ) := lt_of_not_ge hnz
    have hm_le_n : m ≤ n := by
      have : z ≤ (n : ℝ) := le_of_lt hnz'
      have : Nat.ceil z ≤ n := (Nat.ceil_le).2 this
      simpa [m] using this
    have hsum_ge : (n - m : ℝ) ≤ (∑ u ∈ Finset.range n, ind z u) := by
      let S : Finset Nat := (Finset.range (n - m)).map (addLeftEmbedding m)
      have hSsub : S ⊆ Finset.range n := by
        intro u hu
        rcases Finset.mem_map.1 hu with ⟨k, hk, rfl⟩
        have hk_lt : k < n - m := Finset.mem_range.1 hk
        have hk' : m + k < m + (n - m) := Nat.add_lt_add_left hk_lt m
        have hn' : m + (n - m) = n := Nat.add_sub_of_le hm_le_n
        simpa [hn'] using hk'
      have hle : (∑ u ∈ S, ind z u) ≤ (∑ u ∈ Finset.range n, ind z u) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hSsub ?_
        intro u hu hnS
        exact ind_nonneg z u
      have hz_le_m : z ≤ (m : ℝ) := by
        simpa [m] using (Nat.le_ceil z)
      have hSsum : (∑ u ∈ S, ind z u) = (n - m : ℝ) := by
        have hpoint : ∀ u, u ∈ S → ind z u = (1 : ℝ) := by
          intro u hu
          rcases Finset.mem_map.1 hu with ⟨k, hk, rfl⟩
          have hm_le : (m : ℝ) ≤ (m + k : Nat) := by
            exact_mod_cast Nat.le_add_right m k
          have hz_le_nat : z ≤ (m + k : Nat) := le_trans hz_le_m hm_le
          have hz_le : z ≤ (m : ℝ) + (k : ℝ) := by
            simpa [Nat.cast_add] using hz_le_nat
          simp [ind, hz_le]
        calc
          (∑ u ∈ S, ind z u) = (∑ u ∈ S, (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            exact hpoint u hu
          _ = (S.card : ℝ) := by
            simp [Finset.sum_const]
          _ = (n - m : ℝ) := by
            simp [S, Nat.cast_sub hm_le_n]
      have : (n - m : ℝ) ≤ (∑ u ∈ S, ind z u) := by
        simp [hSsum]
      exact le_trans this hle
    have hceil : (m : ℝ) < z + 1 := by
      simpa [m] using (Nat.ceil_lt_add_one (a := z) hz0)
    have hz_gt : (m : ℝ) - 1 < z := by linarith
    have hmain : (n : ℝ) - z ≤ (n : ℝ) - (m : ℝ) + 1 := by linarith
    have hnm : (n : ℝ) - (m : ℝ) = ((n - m : Nat) : ℝ) := by
      simpa using (Nat.cast_sub hm_le_n).symm
    have : (n : ℝ) - z ≤ (1 : ℝ) + ((n - m : Nat) : ℝ) := by
      simpa [hnm, add_comm, add_left_comm, add_assoc] using hmain
    have : (n : ℝ) - z ≤ (1 : ℝ) + (∑ u ∈ Finset.range n, ind z u) := by
      have h1 : (1 : ℝ) + ((n - m : Nat) : ℝ) ≤ (1 : ℝ) + (∑ u ∈ Finset.range n, ind z u) := by
        linarith [hsum_ge]
      exact le_trans this h1
    exact this

/-- Swap a `Fintype` sum with a `range` sum, after pushing multiplication inside. -/
theorem sum_mul_sum_range_eq_sum_range_sum {α : Type u} [Fintype α]
    (n : Nat) (w : α → ℝ) (g : α → Nat → ℝ) :
    (∑ a : α, w a * (∑ u ∈ Finset.range n, g a u))
      = ∑ u ∈ Finset.range n, ∑ a : α, w a * g a u := by
  classical
  have h1 :
      (∑ a : α, w a * (∑ u ∈ Finset.range n, g a u))
        = ∑ a : α, (∑ u ∈ Finset.range n, w a * g a u) := by
    refine Fintype.sum_congr (fun a => w a * (∑ u ∈ Finset.range n, g a u))
      (fun a => (∑ u ∈ Finset.range n, w a * g a u)) ?_
    intro a
    simp [Finset.mul_sum]
  have h2 :
      (∑ a : α, (∑ u ∈ Finset.range n, w a * g a u))
        = ∑ u ∈ Finset.range n, ∑ a : α, w a * g a u := by
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset α)) (t := Finset.range n)
        (f := fun a u => w a * g a u))
  simpa [h1] using h2

/-! ### Geometric series bound `∑ 2^{-(t+1)} ≤ 1` -/

noncomputable def halfSum (n : Nat) : ℝ :=
  ∑ t ∈ Finset.range n, (1 : ℝ) / ((2 : ℝ) ^ (t + 1))

theorem halfSum_succ (n : Nat) :
    halfSum (n + 1) = halfSum n + (1 : ℝ) / ((2 : ℝ) ^ (n + 1)) := by
  classical
  have hnmem : n ∉ Finset.range n := by simp
  simp [halfSum, Finset.range_add_one, hnmem, add_comm]

theorem halfSum_eq (n : Nat) : halfSum n = 1 - (1 : ℝ) / ((2 : ℝ) ^ n) := by
  classical
  induction n with
  | zero =>
      simp [halfSum]
  | succ n ih =>
      have hrec : halfSum (n + 1) = halfSum n + (1 : ℝ) / ((2 : ℝ) ^ (n + 1)) := halfSum_succ n
      have hpow : ((2 : ℝ) ^ (n + 1)) = ((2 : ℝ) ^ n) * 2 := by
        simp [pow_succ]
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ n) := by
        have : (0 : ℝ) < 2 := by norm_num
        exact pow_pos this n
      have hne : ((2 : ℝ) ^ n) ≠ 0 := ne_of_gt hpos
      calc
        halfSum (n + 1)
            = (1 - (1 : ℝ) / ((2 : ℝ) ^ n)) + (1 : ℝ) / ((2 : ℝ) ^ (n + 1)) := by
                simp [hrec, ih]
        _ = 1 - (1 : ℝ) / ((2 : ℝ) ^ (n + 1)) := by
              rw [hpow]
              field_simp [hne]
              ring

theorem halfSum_le_one (n : Nat) : halfSum n ≤ 1 := by
  have h : halfSum n = 1 - (1 : ℝ) / ((2 : ℝ) ^ n) := halfSum_eq n
  have hterm_nonneg : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ n) := by
    have : 0 < ((2 : ℝ) ^ n) := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      exact pow_pos h2 n
    exact one_div_nonneg.mpr (le_of_lt this)
  linarith [h, hterm_nonneg]

/-! ### Event-probability lemmas -/

theorem probTrue_eq_probEvent {α : Type u} [Fintype α] (P : FinDist α) (D : α → Bool) :
    probTrue P D = probEvent P (fun a => D a = true) := by
  classical
  unfold probTrue probEvent
  refine Finset.sum_congr rfl ?_
  intro a ha
  cases hD : D a <;> simp [hD]

theorem probTrue_decide_eq_probEvent {α : Type u} [Fintype α] (P : FinDist α) (E : α → Prop)
    [DecidablePred E] :
    probTrue P (fun a => decide (E a)) = probEvent P E := by
  classical
  unfold probTrue probEvent
  refine Finset.sum_congr rfl ?_
  intro a ha
  by_cases hE : E a <;> simp [hE]

theorem probEvent_le_of_advantage_le {α : Type u} [Fintype α] (P Q : FinDist α)
    (E : α → Prop) [DecidablePred E] (ε : ℝ)
    (h : advantage P Q (fun a => decide (E a)) ≤ ε) :
    probEvent P E ≤ probEvent Q E + ε := by
  classical
  have h' : |probTrue P (fun a => decide (E a)) - probTrue Q (fun a => decide (E a))| ≤ ε := by
    simpa [advantage] using h
  have hsub :
      probTrue P (fun a => decide (E a)) - probTrue Q (fun a => decide (E a)) ≤ ε := by
    exact le_trans (le_abs_self _) h'
  have hle : probTrue P (fun a => decide (E a)) ≤ probTrue Q (fun a => decide (E a)) + ε := by
    exact (sub_le_iff_le_add').1 hsub
  -- Translate `probTrue` to `probEvent`.
  simpa [probTrue_decide_eq_probEvent (P := P) (E := E),
    probTrue_decide_eq_probEvent (P := Q) (E := E)] using hle

/-! ### Uniform counting bound for threshold distinguishers -/

theorem probEvent_uniform_nllBits_le {n : Nat}
    (Q : FinDist (BitStr n)) (hQ : Q.Pos) (u : Nat) (hu : u < n) :
    probEvent (Un n) (fun x : BitStr n => Info.nllBits Q x ≤ (u : ℝ))
      ≤ (1 : ℝ) / ((2 : ℝ) ^ (n - u)) := by
  classical
  let A : Finset (BitStr n) := Finset.univ.filter (fun x : BitStr n => Info.nllBits Q x ≤ (u : ℝ))
  have hprob :
      probEvent (Un n) (fun x : BitStr n => Info.nllBits Q x ≤ (u : ℝ))
        = ∑ x ∈ A, (Un n).pmf x := by
    unfold probEvent
    simp [A, Finset.sum_filter]
  -- For `x ∈ A`, we have `Q.pmf x ≥ 2^{-u}`.
  have hQx : ∀ x, x ∈ A → (1 : ℝ) / ((2 : ℝ) ^ u) ≤ Q.pmf x := by
    intro x hx
    have hx' : Info.nllBits Q x ≤ (u : ℝ) := by
      simpa [A] using (Finset.mem_filter.1 hx).2
    have hlog2_pos : 0 < Real.log (2 : ℝ) := by
      have : (1 : ℝ) < 2 := by norm_num
      simpa using Real.log_pos this
    have hq_pos : 0 < Q.pmf x := hQ x
    -- Rewrite `nllBits` in terms of `Real.log`.
    unfold Info.nllBits Info.nllNat at hx'
    have hsafelog : InfoTheory.safeLog (Q.pmf x) = Real.log (Q.pmf x) :=
      InfoTheory.safeLog_of_pos hq_pos
    have hx'' : -Real.log (Q.pmf x) ≤ (u : ℝ) * Real.log 2 := by
      have := mul_le_mul_of_nonneg_right hx' (le_of_lt hlog2_pos)
      have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      -- `(a / log2) * log2 = a`.
      simpa [hsafelog, div_eq_mul_inv, hlog2_ne0, mul_assoc] using this
    have hxlog : (-(u : ℝ) * Real.log 2) ≤ Real.log (Q.pmf x) := by
      linarith
    -- Convert log-bound to an exp-bound.
    have hexp : Real.exp (-(u : ℝ) * Real.log 2) ≤ Q.pmf x := by
      exact (Real.le_log_iff_exp_le hq_pos).1 hxlog
    have hexp2 : Real.exp (-(↑u * Real.log 2)) ≤ Q.pmf x := by
      have harg : (-(u : ℝ) * Real.log 2) = (-(↑u * Real.log 2) : ℝ) := by simp
      simpa [harg] using hexp
    -- Evaluate `exp (-(u)*log 2)` as `1 / 2^u`.
    have hexp' : Real.exp (-(↑u * Real.log 2)) = (1 : ℝ) / ((2 : ℝ) ^ u) := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have hlog2 : Real.exp (Real.log (2 : ℝ)) = 2 := by
        simpa using Real.exp_log h2pos
      -- `exp (u * log 2) = 2^u`, hence the negated version is the inverse.
      calc
        Real.exp (-(↑u * Real.log 2))
            = (Real.exp (↑u * Real.log 2))⁻¹ := by
                simp [Real.exp_neg]
        _ = (Real.exp (Real.log (2 : ℝ)) ^ u)⁻¹ := by
              -- `exp ((u:ℝ) * x) = exp x ^ u` (Nat exponent form).
              simpa [mul_comm] using (Real.exp_nat_mul (Real.log (2 : ℝ)) u)
        _ = ((2 : ℝ) ^ u)⁻¹ := by simp [hlog2]
        _ = (1 : ℝ) / ((2 : ℝ) ^ u) := by simp [one_div]
    simpa [hexp'] using hexp2
  -- Cardinality bound: `A.card ≤ 2^u`.
  have hcard : (A.card : ℝ) ≤ (2 : ℝ) ^ u := by
    have hsum_le_univ : (∑ x ∈ A, Q.pmf x) ≤ ∑ x : BitStr n, Q.pmf x := by
      have hsub : A ⊆ (Finset.univ : Finset (BitStr n)) := by
        intro x hx
        simp
      have :
          (∑ x ∈ A, Q.pmf x) ≤ ∑ x ∈ (Finset.univ : Finset (BitStr n)), Q.pmf x := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro x hx hnA
        exact Q.nonneg x
      simpa using this
    have hsum_ge_const :
        (A.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ u)) ≤ ∑ x ∈ A, Q.pmf x := by
      have hsum : (∑ _x ∈ A, (1 : ℝ) / ((2 : ℝ) ^ u)) ≤ ∑ x ∈ A, Q.pmf x := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact hQx x hx
      simpa [Finset.sum_const] using hsum
    have hsum_le_one : (∑ x ∈ A, Q.pmf x) ≤ 1 := by
      -- `∑ x, Q.pmf x = 1`.
      simpa [Q.sum_one] using hsum_le_univ
    have hmul_le_one :
        (A.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ u)) ≤ 1 := le_trans hsum_ge_const hsum_le_one
    have hden_pos : 0 < ((2 : ℝ) ^ u) := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      exact pow_pos h2 u
    -- Divide by `1 / 2^u` (equivalently multiply by `2^u`).
    have :
        (A.card : ℝ) ≤ 1 / ((1 : ℝ) / ((2 : ℝ) ^ u)) := by
      -- `a ≤ 1 / c` iff `a * c ≤ 1`.
      have hcpos : 0 < (1 : ℝ) / ((2 : ℝ) ^ u) := by
        exact one_div_pos.mpr hden_pos
      have : (A.card : ℝ) ≤ 1 / ((1 : ℝ) / ((2 : ℝ) ^ u)) ↔
          (A.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ u)) ≤ 1 := by
        simpa using (le_div_iff₀ (a := (A.card : ℝ)) (b := (1 : ℝ))
          (c := (1 : ℝ) / ((2 : ℝ) ^ u)) hcpos)
      exact (this).2 hmul_le_one
    -- Simplify `1 / (1 / 2^u) = 2^u`.
    simpa [one_div, inv_inv] using this
  -- Conclude uniform probability bound using `A.card / 2^n`.
  have hpmf : ∀ x : BitStr n, (Un n).pmf x = 1 / ((2 : ℝ) ^ n) := by
    intro x
    -- `Fintype.card (BitStr n) = 2^n`.
    simp [Un, Epiplexity.FinDist.uniform, BitStr]
  have hsumA :
      (∑ x ∈ A, (Un n).pmf x) = (A.card : ℝ) * (1 / ((2 : ℝ) ^ n)) := by
    simp [hpmf, Finset.sum_const]
  -- Use `A.card ≤ 2^u`.
  have hratio :
      (A.card : ℝ) * (1 / ((2 : ℝ) ^ n)) ≤ ((2 : ℝ) ^ u) * (1 / ((2 : ℝ) ^ n)) := by
    exact mul_le_mul_of_nonneg_right hcard (by
      have h2 : 0 ≤ (1 / ((2 : ℝ) ^ n)) := by
        have h2pos : 0 < ((2 : ℝ) ^ n) := by
          have h0 : (0 : ℝ) < 2 := by norm_num
          exact pow_pos h0 n
        exact one_div_nonneg.mpr (le_of_lt h2pos)
      exact h2)
  have hpow_div :
      ((2 : ℝ) ^ u) * (1 / ((2 : ℝ) ^ n)) = (1 : ℝ) / ((2 : ℝ) ^ (n - u)) := by
    have hu_le : u ≤ n := Nat.le_of_lt hu
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have hnpos : 0 < ((2 : ℝ) ^ n) := pow_pos h2pos n
    have huneq : ((2 : ℝ) ^ n) ≠ 0 := ne_of_gt hnpos
    -- `2^n = 2^u * 2^(n-u)`.
    have hpow : ((2 : ℝ) ^ n) = ((2 : ℝ) ^ u) * ((2 : ℝ) ^ (n - u)) := by
      simpa [pow_add, Nat.add_sub_of_le hu_le, mul_assoc, mul_left_comm, mul_comm] using
        (pow_add (2 : ℝ) u (n - u))
    calc
      ((2 : ℝ) ^ u) * (1 / ((2 : ℝ) ^ n))
          = ((2 : ℝ) ^ u) / ((2 : ℝ) ^ n) := by simp [div_eq_mul_inv]
      _ = ((2 : ℝ) ^ u) / (((2 : ℝ) ^ u) * ((2 : ℝ) ^ (n - u))) := by simp [hpow]
      _ = 1 / ((2 : ℝ) ^ (n - u)) := by
            field_simp [huneq]
      _ = (1 : ℝ) / ((2 : ℝ) ^ (n - u)) := by simp
  -- Put it together.
  have : (∑ x ∈ A, (Un n).pmf x) ≤ (1 : ℝ) / ((2 : ℝ) ^ (n - u)) := by
    calc
      (∑ x ∈ A, (Un n).pmf x)
          = (A.card : ℝ) * (1 / ((2 : ℝ) ^ n)) := hsumA
      _ ≤ ((2 : ℝ) ^ u) * (1 / ((2 : ℝ) ^ n)) := hratio
      _ = (1 : ℝ) / ((2 : ℝ) ^ (n - u)) := hpow_div
  simpa [hprob] using this

/-! ### Theorem 17 (paper): near-maximal time-bounded entropy for CSPRNG outputs -/

theorem crossEntropyBits_ge_csprng {k n T : Nat} (G : BitStr k → BitStr n) (ε : Nat → ℝ)
    (hCSPRNG : CSPRNGSecure (k := k) (n := n) (T := T) G ε)
    (P : Prog (BitStr n)) (hP : Prog.Feasible T P) :
    (n : ℝ) - 2 - (n : ℝ) * ε k ≤
      Info.crossEntropyBits (prgDist (k := k) (n := n) G) P.dist := by
  classical
  let X : FinDist (BitStr n) := prgDist (k := k) (n := n) G
  let U : FinDist (BitStr n) := Un n
  -- Apply the layercake inequality to `L(x) = nllBits(P.dist) x`.
  have hlayer :
      (n : ℝ) - (∑ x : BitStr n, X.pmf x * Info.nllBits P.dist x)
        ≤ (1 : ℝ) + ∑ u ∈ Finset.range n,
            probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)) := by
    -- Sum the pointwise inequality against `X`.
    have hpoint :
        ∀ x : BitStr n,
          X.pmf x * ((n : ℝ) - Info.nllBits P.dist x)
            ≤ X.pmf x * ((1 : ℝ) + (∑ u ∈ Finset.range n, ind (Info.nllBits P.dist x) u)) := by
      intro x
      have hnll_nonneg : 0 ≤ Info.nllBits P.dist x := Info.nllBits_nonneg (q := P.dist) P.distPos x
      have := layercake_pointwise (n := n) (z := Info.nllBits P.dist x) hnll_nonneg
      exact mul_le_mul_of_nonneg_left this (X.nonneg x)
    have hsum :
        (∑ x : BitStr n, X.pmf x * ((n : ℝ) - Info.nllBits P.dist x))
          ≤ ∑ x : BitStr n, X.pmf x *
              ((1 : ℝ) + (∑ u ∈ Finset.range n, ind (Info.nllBits P.dist x) u)) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hpoint x
    -- Rewrite the LHS as `n - E[L]`.
    have hLHS :
        (∑ x : BitStr n, X.pmf x * ((n : ℝ) - Info.nllBits P.dist x))
          = (n : ℝ) - (∑ x : BitStr n, X.pmf x * Info.nllBits P.dist x) := by
      calc
        (∑ x : BitStr n, X.pmf x * ((n : ℝ) - Info.nllBits P.dist x))
            = (∑ x : BitStr n, X.pmf x * (n : ℝ)) -
                (∑ x : BitStr n, X.pmf x * Info.nllBits P.dist x) := by
                  simp [mul_sub, Finset.sum_sub_distrib]
        _ = (n : ℝ) * (∑ x : BitStr n, X.pmf x) -
              (∑ x : BitStr n, X.pmf x * Info.nllBits P.dist x) := by
                have hsum :
                    (∑ x : BitStr n, X.pmf x * (n : ℝ))
                      = (n : ℝ) * (∑ x : BitStr n, X.pmf x) := by
                  have h' :
                      (∑ x : BitStr n, X.pmf x * (n : ℝ))
                        = (∑ x : BitStr n, X.pmf x) * (n : ℝ) := by
                    simpa using
                      (Finset.sum_mul (s := (Finset.univ : Finset (BitStr n)))
                        (f := fun x : BitStr n => X.pmf x) (a := (n : ℝ))).symm
                  simpa [mul_comm, mul_left_comm, mul_assoc] using h'
                simp [hsum]
        _ = (n : ℝ) - (∑ x : BitStr n, X.pmf x * Info.nllBits P.dist x) := by
              simp [X.sum_one]
    -- Rewrite the RHS as `1 + ∑_u probEvent`.
    have hRHS :
        (∑ x : BitStr n, X.pmf x *
            ((1 : ℝ) + (∑ u ∈ Finset.range n, ind (Info.nllBits P.dist x) u)))
          =
            (1 : ℝ) + ∑ u ∈ Finset.range n,
              probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)) := by
      -- Split the outer sum and swap the order of summation.
      calc
        (∑ x : BitStr n, X.pmf x *
            ((1 : ℝ) + (∑ u ∈ Finset.range n, ind (Info.nllBits P.dist x) u)))
            = (∑ x : BitStr n, X.pmf x * (1 : ℝ)) +
                (∑ x : BitStr n, X.pmf x * (∑ u ∈ Finset.range n, ind (Info.nllBits P.dist x) u)) := by
                  simp [mul_add, Finset.sum_add_distrib]
        _ = (1 : ℝ) +
              (∑ x : BitStr n, X.pmf x * (∑ u ∈ Finset.range n, ind (Info.nllBits P.dist x) u)) := by
              simp [X.sum_one]
        _ = (1 : ℝ) +
              (∑ u ∈ Finset.range n, ∑ x : BitStr n, X.pmf x * ind (Info.nllBits P.dist x) u) := by
              -- swap sums
              refine congrArg (fun r => (1 : ℝ) + r) ?_
              -- use `sum_mul_sum_range_eq_sum_range_sum`
              simpa [ind] using
                (sum_mul_sum_range_eq_sum_range_sum (α := BitStr n) (n := n)
                  (w := fun x : BitStr n => X.pmf x)
                  (g := fun x u => ind (Info.nllBits P.dist x) u))
        _ = (1 : ℝ) + ∑ u ∈ Finset.range n,
              probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)) := by
              -- `probEvent` is the sum of pmf over the event; here we have `pmf * 0/1`.
              refine congrArg (fun r => (1 : ℝ) + r) ?_
              refine Finset.sum_congr rfl ?_
              intro u hu
              unfold probEvent
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases hxu : Info.nllBits P.dist x ≤ (u : ℝ)
              · simp [ind, hxu]
              · simp [ind, hxu]
    -- Put everything together.
    have := hsum
    simpa [hLHS, hRHS] using this
  -- Turn the sum on the LHS into `crossEntropyBits`.
  have hce : ∑ x : BitStr n, X.pmf x * Info.nllBits P.dist x = Info.crossEntropyBits X P.dist := by
    rfl
  -- Bound each threshold probability using CSPRNG security.
  have hbound_each :
      ∀ u : Nat, u < n →
        probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ))
          ≤ (1 : ℝ) / ((2 : ℝ) ^ (n - u)) + ε k := by
    intro u hu
    have hUu :
        probEvent U (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ))
          ≤ (1 : ℝ) / ((2 : ℝ) ^ (n - u)) :=
      probEvent_uniform_nllBits_le (n := n) (Q := P.dist) P.distPos u hu
    -- Apply indistinguishability to the distinguisher `x ↦ 1{nllBits ≤ u}`.
    let D : Distinguisher (BitStr n) :=
      { run := fun x => decide (Info.nllBits P.dist x ≤ (u : ℝ))
        runtime := 0 }
    have hAdv :
        advantage X U D.run ≤ ε k := by
      -- `D.runtime = 0 ≤ T` so `CSPRNGSecure` applies.
      have hRT : D.runtime ≤ T := by simp [D]
      simpa [X, U, prgDist, Un] using hCSPRNG D hRT
    have hPX : probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ))
        ≤ probEvent U (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)) + ε k :=
      probEvent_le_of_advantage_le (P := X) (Q := U)
        (E := fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)) (ε := ε k) hAdv
    exact le_trans hPX (by linarith)
  -- Sum the bounds.
  have hsum_prob :
      (∑ u ∈ Finset.range n,
          probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)))
        ≤ (∑ u ∈ Finset.range n, (1 : ℝ) / ((2 : ℝ) ^ (n - u))) + (n : ℝ) * ε k := by
    -- split the sum and bound each term
    have :
        (∑ u ∈ Finset.range n,
            probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)))
          ≤
        (∑ u ∈ Finset.range n,
            ((1 : ℝ) / ((2 : ℝ) ^ (n - u)) + ε k)) := by
      refine Finset.sum_le_sum ?_
      intro u hu
      have hu' : u < n := Finset.mem_range.1 hu
      exact hbound_each u hu'
    -- simplify RHS
    calc
      (∑ u ∈ Finset.range n,
          probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)))
          ≤ (∑ u ∈ Finset.range n, ((1 : ℝ) / ((2 : ℝ) ^ (n - u)) + ε k)) := this
      _ = (∑ u ∈ Finset.range n, (1 : ℝ) / ((2 : ℝ) ^ (n - u))) + (n : ℝ) * ε k := by
            simp [Finset.sum_add_distrib]
  -- Bound the geometric sum by `1`.
  have hgeom :
      (∑ u ∈ Finset.range n, (1 : ℝ) / ((2 : ℝ) ^ (n - u))) ≤ 1 := by
    -- Reindex using `sum_range_reflect` to match `halfSum`.
    cases n with
    | zero =>
        simp
    | succ n =>
        have hEq :
            (∑ u ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ ((n + 1) - u)))
              =
            (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ (j + 1))) := by
          have hreflect :=
            (Finset.sum_range_reflect (f := fun j : Nat => (1 : ℝ) / ((2 : ℝ) ^ (j + 1))) (n := n + 1))
          have hrewrite :
              (∑ u ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ ((n + 1) - u)))
                =
              (∑ u ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ ((n - u) + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            have hu_le : u ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hu)
            have hsub : (n + 1) - u = (n - u) + 1 := by
              simpa [Nat.succ_eq_add_one] using (Nat.succ_sub (m := n) (n := u) hu_le)
            simp [hsub]
          calc
            (∑ u ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ ((n + 1) - u)))
                =
              (∑ u ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ ((n - u) + 1))) := hrewrite
            _ = (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ (j + 1))) := by
                simpa [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hreflect
        have hhalf : halfSum (n + 1) ≤ 1 := halfSum_le_one (n + 1)
        have hhalf' : (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ (j + 1))) ≤ 1 := by
          dsimp [halfSum] at hhalf
          exact hhalf
        calc
          (∑ u ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ ((n + 1) - u)))
              = (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / ((2 : ℝ) ^ (j + 1))) := hEq
          _ ≤ 1 := hhalf'
  -- Put bounds into the layercake inequality.
  have hlayer' :
      (n : ℝ) - Info.crossEntropyBits X P.dist
        ≤ (1 : ℝ) + 1 + (n : ℝ) * ε k := by
    -- substitute `hce` and bound the probability sum
    have : (n : ℝ) - Info.crossEntropyBits X P.dist
        ≤ (1 : ℝ) +
          ((∑ u ∈ Finset.range n, (1 : ℝ) / ((2 : ℝ) ^ (n - u))) + (n : ℝ) * ε k) := by
      have := hlayer
      -- replace the inner sum using `hsum_prob`
      have hprob_sum :
          (∑ u ∈ Finset.range n,
              probEvent X (fun x : BitStr n => Info.nllBits P.dist x ≤ (u : ℝ)))
            ≤ (∑ u ∈ Finset.range n, (1 : ℝ) / ((2 : ℝ) ^ (n - u))) + (n : ℝ) * ε k := hsum_prob
      -- apply monotonicity of addition
      exact le_trans (by simpa [hce] using this) (by linarith)
    -- apply `hgeom`
    linarith [this, hgeom]
  -- Rearrange to the desired entropy lower bound.
  have hfinal :
      (n : ℝ) - 2 - (n : ℝ) * ε k ≤ Info.crossEntropyBits X P.dist := by
    linarith [hlayer']
  simpa [X] using hfinal

theorem theorem17 {k n T : Nat} (G : BitStr k → BitStr n) (ε : Nat → ℝ)
    (hCSPRNG : CSPRNGSecure (k := k) (n := n) (T := T) G ε) :
    ∀ opt : OptimalProg (α := BitStr n) T (prgDist (k := k) (n := n) G),
      (n : ℝ) - 2 - (n : ℝ) * ε k ≤ opt.HT := by
  intro opt
  have h := crossEntropyBits_ge_csprng (k := k) (n := n) (T := T) G ε hCSPRNG opt.P opt.feasible
  simpa [OptimalProg.HT] using h

/-! ### Theorem 19 (paper): low epiplexity for CSPRNG outputs -/

theorem theorem19 {k n T : Nat} (G : BitStr k → BitStr n) (ε : Nat → ℝ)
    (hCSPRNG : CSPRNGSecure (k := k) (n := n) (T := T) G ε) :
    ∀ opt : OptimalProg (α := BitStr n) T (prgDist (k := k) (n := n) G),
      (opt.ST : ℝ) ≤ (3 : ℝ) + (n : ℝ) * ε k := by
  intro opt
  have hHT : (n : ℝ) - 2 - (n : ℝ) * ε k ≤ opt.HT := theorem17 (k := k) (n := n) (T := T)
    (G := G) (ε := ε) hCSPRNG opt
  -- Upper bound on total MDL using the uniform witness.
  have hFeas : Prog.Feasible T (BitStr.uniformProg n) := by
    simp [BitStr.uniformProg, Prog.Feasible]
  have hopt :
      mdlCost (prgDist (k := k) (n := n) G) opt.P
        ≤ mdlCost (prgDist (k := k) (n := n) G) (BitStr.uniformProg n) :=
    opt.optimal (BitStr.uniformProg n) hFeas
  have hce_unif :
      Info.crossEntropyBits (prgDist (k := k) (n := n) G) (BitStr.uniformProg n).dist = n := by
    simpa [BitStr.uniformProg] using
      (BitStr.crossEntropyBits_uniform (n := n) (X := prgDist (k := k) (n := n) G))
  have hcost_rhs :
      mdlCost (prgDist (k := k) (n := n) G) (BitStr.uniformProg n)
        = (BitStr.uniformProg n).codeLen + (n : ℝ) := by
      simp [mdlCost, hce_unif]
  have hcost_lhs :
      mdlCost (prgDist (k := k) (n := n) G) opt.P = (opt.ST : ℝ) + opt.HT := by
    simp [mdlCost, OptimalProg.ST, OptimalProg.HT]
  have hsum : (opt.ST : ℝ) + opt.HT ≤ (BitStr.uniformProg n).codeLen + (n : ℝ) := by
    simpa [hcost_lhs, hcost_rhs] using hopt
  have hST : (opt.ST : ℝ) ≤ (BitStr.uniformProg n).codeLen + (n : ℝ) - opt.HT := by
    linarith
  -- Use the entropy lower bound.
  have hcode : (BitStr.uniformProg n).codeLen = 1 := BitStr.uniformProg_codeLen n
  -- Bound by constants: `n+1 - (n - 2 - nε) = 3 + nε`.
  have hcodeR : ((BitStr.uniformProg n).codeLen : ℝ) = 1 := by exact_mod_cast hcode
  linarith [hST, hHT, hcodeR]

/-! ### Theorem 9 (paper): combined entropy + epiplexity bounds -/

theorem theorem9 {k n T : Nat} (G : BitStr k → BitStr n) (ε : Nat → ℝ)
    (hCSPRNG : CSPRNGSecure (k := k) (n := n) (T := T) G ε) :
    ∀ opt : OptimalProg (α := BitStr n) T (prgDist (k := k) (n := n) G),
      ((n : ℝ) - 2 - (n : ℝ) * ε k ≤ opt.HT) ∧
        (opt.HT ≤ (n : ℝ) + (BitStr.uniformProg n).codeLen) ∧
        ((opt.ST : ℝ) ≤ (3 : ℝ) + (n : ℝ) * ε k) := by
  intro opt
  have hHTlow : (n : ℝ) - 2 - (n : ℝ) * ε k ≤ opt.HT :=
    theorem17 (k := k) (n := n) (T := T) (G := G) (ε := ε) hCSPRNG opt
  -- upper bound on HT via MDL optimality against the uniform witness
  have hFeas : Prog.Feasible T (BitStr.uniformProg n) := by
    simp [BitStr.uniformProg, Prog.Feasible]
  have hopt :
      mdlCost (prgDist (k := k) (n := n) G) opt.P
        ≤ mdlCost (prgDist (k := k) (n := n) G) (BitStr.uniformProg n) :=
    opt.optimal (BitStr.uniformProg n) hFeas
  have hce_unif :
      Info.crossEntropyBits (prgDist (k := k) (n := n) G) (BitStr.uniformProg n).dist = n := by
    simpa [BitStr.uniformProg] using
      (BitStr.crossEntropyBits_uniform (n := n) (X := prgDist (k := k) (n := n) G))
  have hcost_rhs :
      mdlCost (prgDist (k := k) (n := n) G) (BitStr.uniformProg n)
        = (BitStr.uniformProg n).codeLen + (n : ℝ) := by
      simp [mdlCost, hce_unif]
  have hcost_lhs :
      mdlCost (prgDist (k := k) (n := n) G) opt.P = (opt.ST : ℝ) + opt.HT := by
    simp [mdlCost, OptimalProg.ST, OptimalProg.HT]
  have hsum : (opt.ST : ℝ) + opt.HT ≤ (BitStr.uniformProg n).codeLen + (n : ℝ) := by
    simpa [hcost_lhs, hcost_rhs] using hopt
  have hSTnonneg : 0 ≤ (opt.ST : ℝ) := by
    exact_mod_cast Nat.zero_le opt.ST
  have hHTup : opt.HT ≤ (BitStr.uniformProg n).codeLen + (n : ℝ) := by
    exact le_of_add_le_of_nonneg_right hsum hSTnonneg
  have hHTup' : opt.HT ≤ (n : ℝ) + (BitStr.uniformProg n).codeLen := by
    simpa [add_comm, add_left_comm, add_assoc] using hHTup
  have hSTup : (opt.ST : ℝ) ≤ (3 : ℝ) + (n : ℝ) * ε k :=
    theorem19 (k := k) (n := n) (T := T) (G := G) (ε := ε) hCSPRNG opt
  exact ⟨hHTlow, hHTup', hSTup⟩

/-! ### Theorems 12/18 (paper): deterministic transformation can increase time-bounded entropy -/

theorem theorem12 {k n T : Nat} (G : BitStr k → BitStr n) (ε : Nat → ℝ)
    (hCSPRNG : CSPRNGSecure (k := k) (n := n) (T := T) G ε) :
    ∀ optG : OptimalProg (α := BitStr n) T (prgDist (k := k) (n := n) G),
      ∀ optU : OptimalProg (α := BitStr k) T (Un k),
        optG.HT ≥ optU.HT + (n : ℝ) - (k : ℝ) - (n : ℝ) * ε k - 3 := by
  intro optG optU
  have hG : optG.HT ≥ (n : ℝ) - 2 - (n : ℝ) * ε k :=
    theorem17 (k := k) (n := n) (T := T) (G := G) (ε := ε) hCSPRNG optG
  have hU : optU.HT ≤ (k : ℝ) + (BitStr.uniformProg k).codeLen := by
    -- from Lemma 16 specialized to `BitStr k`
    have := BitStr.lemma16_HT_bounds (n := k) (T := T)
    have h := (this optU).2
    simpa [Un, add_comm, add_left_comm, add_assoc] using h
  have hcode : (BitStr.uniformProg k).codeLen = 1 := BitStr.uniformProg_codeLen k
  -- combine (constants are loose, matching the paper's `O(1)` slack)
  have hcodeR : ((BitStr.uniformProg k).codeLen : ℝ) = 1 := by exact_mod_cast hcode
  linarith [hG, hU, hcodeR]

theorem theorem18 {k n T : Nat} (G : BitStr k → BitStr n) (ε : Nat → ℝ)
    (hCSPRNG : CSPRNGSecure (k := k) (n := n) (T := T) G ε) :
    ∀ optG : OptimalProg (α := BitStr n) T (prgDist (k := k) (n := n) G),
      ∀ optU : OptimalProg (α := BitStr k) T (Un k),
        optG.HT ≥ optU.HT + (n : ℝ) - (k : ℝ) - (n : ℝ) * ε k - 3 := by
  exact theorem12 (k := k) (n := n) (T := T) (G := G) (ε := ε) hCSPRNG

end CSPRNG

end

end Crypto
end Epiplexity
end HeytingLean
