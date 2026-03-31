import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Tactic
import Batteries.Data.List.Basic
import HeytingLean.Math.ProbVec

/-!
# QAI Information (Real)

Executable-friendly information quantities for discrete (finite) models:
- KL divergence (guarded for domain issues via `safeLog`)
- Expected free energy scaffold and a trivial decomposition lemma (by definition)
- A simple `argminIdx` on lists to pick a best action witness

This module is deliberately split into two layers:

* a light executable layer (Float/ℝ arrays with guarded `safeLog`),
* and a slowly growing proof layer for discrete KL and EFE.  In this
  proof layer we now establish both diagonal nonnegativity and a
  Gibbs-style inequality for discrete KL under explicit probability
  assumptions (`KLAssumptions`), together with small Real-level
  identities.
-/

namespace HeytingLean
namespace Quantum
namespace ActiveInference

noncomputable section

open InformationTheory

def safeLog (x : ℝ) : ℝ := if x > 0 then Real.log x else 0

def klTerm (p q : ℝ) : ℝ :=
  if p ≤ 0 then 0 else p * (safeLog p - safeLog q)

def arrZipWith (f : ℝ → ℝ → ℝ) (xs ys : Array ℝ) : Array ℝ := Id.run do
  let n := min xs.size ys.size
  let mut out := Array.mkEmpty n
  for i in [:n] do
    out := out.push (f xs[i]! ys[i]!)
  out

@[simp] def arrSum (xs : Array ℝ) : ℝ := Id.run do
  let mut s := 0.0
  for i in [:xs.size] do s := s + xs[i]!
  s

/-! A list-based KL that is convenient for proofs. -/

noncomputable def klDivL : List ℝ → List ℝ → ℝ
  | [], _ => 0
  | _::_, [] => 0
  | p :: ps, q :: qs => klTerm p q + klDivL ps qs

def klDivR (p q : Array ℝ) : ℝ :=
  klDivL p.toList q.toList

/-! A proof-oriented alias for array inputs via lists (defined after nonneg lemma). -/
@[simp] theorem klDivR_eq_alias (p q : Array ℝ) : klDivR p q = klDivL p.toList q.toList := rfl

noncomputable def sumQPosRec : List ℝ → List ℝ → ℝ
  | [], _ => 0
  | _::_, [] => 0
  | p :: ps, q :: qs => (if 0 < p then q else 0) + sumQPosRec ps qs

noncomputable def lowerBoundRec : List ℝ → List ℝ → ℝ
  | [], _ => 0
  | _::_, [] => 0
  | p :: ps, q :: qs => (if 0 < p then p - q else 0) + lowerBoundRec ps qs

/-! Basic, easy lemmas -/

/-! ### `safeLog` and per-coordinate KL helpers -/

lemma safeLog_of_pos {x : ℝ} (hx : 0 < x) : safeLog x = Real.log x := by
  simp [safeLog, hx]

lemma safeLog_of_nonpos {x : ℝ} (hx : x ≤ 0) : safeLog x = 0 := by
  have hx' : ¬ x > 0 := not_lt_of_ge hx
  simp [safeLog, hx']

lemma klTerm_of_pos {p q : ℝ} (hp : 0 < p) :
    klTerm p q = p * (safeLog p - safeLog q) := by
  have : ¬ p ≤ 0 := not_le_of_gt hp
  simp [klTerm, this]

/-- One-dimensional Gibbs-style lower bound for a single KL term.

Under the mild probability-style assumptions `0 ≤ p` and `0 < q`,
the guarded term `klTerm p q` dominates the affine lower bound
`(if 0 < p then p - q else 0)`.  The `if` matches the convention
`0 * log (0 / q) = 0` at zero mass. -/
lemma klTerm_ge_if_pos_sub (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) :
    klTerm p q ≥ (if 0 < p then p - q else 0) := by
  classical
  by_cases hp0 : p ≤ 0
  · -- In this case `p = 0` by nonnegativity and `klTerm` is zero.
    have hp_eq : p = 0 := le_antisymm hp0 hp
    have h_if : (if 0 < p then p - q else 0) = 0 := by
      have : ¬ 0 < p := by
        exact not_lt_of_ge hp0
      simp [this]
    simp [klTerm, hp0, h_if]
  · -- Here `p > 0`, and we appeal to `Real.log_le_sub_one_of_pos`.
    have hp_pos : 0 < p := lt_of_not_ge hp0
    have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
    -- Start from `log x ≤ x - 1` at `x = q/p`.
    have h_base :
        Real.log (q / p) ≤ q / p - 1 :=
      Real.log_le_sub_one_of_pos (show 0 < q / p from div_pos hq hp_pos)
    -- Multiply by `p > 0` on the left.
    have h_mul :
        p * Real.log (q / p) ≤ p * (q / p - 1) :=
      mul_le_mul_of_nonneg_left h_base (le_of_lt hp_pos)
    -- Rewrite the left-hand side via `log_div`.
    have h_mul' :
        p * (Real.log q - Real.log p) ≤ p * (q / p - 1) := by
      -- `Real.log (q/p) = log q - log p` for nonzero `p, q`.
      have h_log_div :
          Real.log (q / p) = Real.log q - Real.log p :=
        Real.log_div (by exact ne_of_gt hq) (by exact hp_ne)
      simpa [h_log_div] using h_mul
    -- Simplify the right-hand side to `q - p`.
    have h_simplify :
        p * (q / p - 1) = q - p := by
      have h1 : p * (q / p) = q := by
        -- `p * (q/p) = q` for `p ≠ 0`.
        -- Rewrite `p * (q/p)` into `q * p * p⁻¹` and cancel the `p`.
        have hp_ne' : (p : ℝ) ≠ 0 := hp_ne
        have h' :
            p * (q / p) = q * p * p⁻¹ := by
          have : p * (q / p) = p * (q * p⁻¹) := by
            simp [div_eq_mul_inv]
          -- Commute and reassociate to `q * p * p⁻¹`.
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have h_cancel :
            q * p * p⁻¹ = q :=
          mul_inv_cancel_right₀ (a := q) hp_ne'
        calc
          p * (q / p)
              = q * p * p⁻¹ := h'
          _ = q := h_cancel
      have h2 : p * (1 : ℝ) = p := by simp
      -- Using `p * (q/p - 1) = p * (q/p) - p * 1`.
      calc
        p * (q / p - 1) = p * (q / p) - p * (1 : ℝ) := by
          simpa [mul_sub_left_distrib]
        _ = q - p := by simpa [h1, h2]
    -- Combine and flip the inequality.
    have h_le : p * (Real.log q - Real.log p) ≤ q - p := by
      simpa [h_simplify] using h_mul'
    have h_ge :
        p * (Real.log p - Real.log q) ≥ p - q := by
      -- This goal is definitionally `p - q ≤ p * (log p - log q)`.
      have h_neg := neg_le_neg h_le
      -- Rewrite both sides of `h_neg` into the desired form.
      have h_left : -(q - p) = p - q := by
        ring_nf
      have h_right :
          -(p * (Real.log q - Real.log p)) =
            p * (Real.log p - Real.log q) := by
        ring_nf
      have : p - q ≤ p * (Real.log p - Real.log q) := by
        simpa [h_left, h_right] using h_neg
      exact this
    -- Now rewrite `klTerm` in terms of `Real.log` via `safeLog`.
    have h_safe_p : safeLog p = Real.log p := safeLog_of_pos hp_pos
    have h_safe_q : safeLog q = Real.log q := safeLog_of_pos hq
    have h_kl :
        klTerm p q = p * (Real.log p - Real.log q) := by
      have := klTerm_of_pos (p := p) (q := q) hp_pos
      simpa [h_safe_p, h_safe_q] using this
    have h_if : (if 0 < p then p - q else 0) = p - q := by
      have : 0 < p := hp_pos
      simp [this]
    -- Put everything together.
    simpa [h_kl, h_if] using h_ge

lemma klTerm_self_zero {p : ℝ} : klTerm p p = 0 := by
  by_cases hp : p ≤ 0
  · simp [klTerm, hp]
  · have hpos : 0 < p := lt_of_not_ge hp
    have : safeLog p = Real.log p := by simp [safeLog, hpos]
    simp [klTerm, hp, this]

@[simp] lemma klDivL_self_zero (ps : List ℝ) : klDivL ps ps = 0 := by
  induction ps with
  | nil => simp [klDivL]
  | cons p ps ih =>
      simp [klDivL, klTerm_self_zero, ih]

@[simp] lemma klDivR_self_zero (p : Array ℝ) : klDivR p p = 0 := by
  simp [klDivR, klDivL_self_zero]

/-! Minimal nonnegativity lemmas (diagonal case), kept lightweight.
    These specialise the discrete KL scaffold to the case where the
    two arguments coincide.  General Gibbs-style nonnegativity for
    arbitrary probability vectors is developed in the following
    section under explicit Real-level assumptions. -/

lemma klDivL_self_nonneg (ps : List ℝ) : 0 ≤ klDivL ps ps := by
  have h := klDivL_self_zero ps
  simpa [h]

lemma klDivR_self_nonneg (p : Array ℝ) : 0 ≤ klDivR p p := by
  have h := klDivR_self_zero p
  simpa [h]

/-- Relate a single guarded KL term to the standard `klFun` integrand.

For nonnegative `p` and strictly positive `q`, the scalar contribution
`klTerm p q` decomposes as
`q * klFun (p / q) - (q - p)`, where `klFun x = x * log x + 1 - x`.
This is the usual `q * klFun (p/q)` representation of discrete KL,
plus a linear correction term that telescopes when we sum over all
coordinates and use the fact that total mass is preserved. -/
lemma klTerm_eq_q_mul_klFun_sub (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) :
    klTerm p q = q * klFun (p / q) - (q - p) := by
  classical
  by_cases hp0 : p = 0
  · -- In the zero-mass case, both sides vanish by definition.
    subst hp0
    -- Left-hand side: guarded `klTerm` is zero at `p = 0`.
    have hL : klTerm 0 q = 0 := by
      simp [klTerm]
    -- Right-hand side: `q * klFun (0/q) - (q - 0) = 0`.
    have hR : q * klFun (0 / q) - (q - 0) = 0 := by
      -- `0 / q = 0` and `klFun 0 = 1`, so the expression simplifies.
      have : (0 : ℝ) / q = 0 := by
        simp
      simp [klFun, this]
    -- Conclude equality since both sides are zero.
    calc
      klTerm 0 q = 0 := hL
      _ = q * klFun (0 / q) - (q - 0) := hR.symm
  · -- Positive-mass case: rewrite everything in terms of logarithms.
    have hp_pos : 0 < p := lt_of_le_of_ne hp (by
      intro h0
      exact hp0 h0.symm)
    have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq
    -- Rewrite the guarded term using `Real.log`.
    have h_safe_p : safeLog p = Real.log p := safeLog_of_pos hp_pos
    have h_safe_q : safeLog q = Real.log q := safeLog_of_pos hq
    have h_klTerm :
        klTerm p q = p * (Real.log p - Real.log q) := by
      have := klTerm_of_pos (p := p) (q := q) hp_pos
      simpa [h_safe_p, h_safe_q] using this
    -- Expand the right-hand side via the definition of `klFun`.
    have h_log_div :
        Real.log (p / q) = Real.log p - Real.log q :=
      Real.log_div (by exact ne_of_gt hp_pos) hq_ne
    have hR :
        q * klFun (p / q) - (q - p) =
          p * (Real.log p - Real.log q) := by
      -- Expand and simplify algebraically.
      unfold klFun
      -- First work at `log (p/q)` scale, then substitute.
      have : q * ((p / q) * Real.log (p / q) + 1 - p / q) - (q - p)
              = p * (Real.log (p / q)) := by
        -- Expand and simplify using `q ≠ 0`.
        calc
          q * ((p / q) * Real.log (p / q) + 1 - p / q) - (q - p)
              = q * (p / q) * Real.log (p / q) + q * 1 - q * (p / q) - (q - p) := by
                ring
          _ = p * Real.log (p / q) + q - p - (q - p) := by
                have hqp : q * (p / q) = p := by
                  field_simp [div_eq_mul_inv, hq_ne]
                have hqp' :
                    q * (p / q) * Real.log (p / q) =
                      p * Real.log (p / q) := by
                  simpa [hqp, mul_comm, mul_left_comm, mul_assoc]
                simp [hqp, hqp']
          _ = p * Real.log (p / q) := by ring
      simpa [klFun, h_log_div] using this
    -- Combine both sides: both sides equal `p * (log p - log q)`.
    calc
      klTerm p q = p * (Real.log p - Real.log q) := h_klTerm
      _ = q * klFun (p / q) - (q - p) := by simpa [hR.symm]

/-- A list of the `qᵢ * klFun (pᵢ / qᵢ)` contributions for a pair of lists.

This list is aligned with the recursive definition of `klDivL` and
is used to express discrete KL as a sum of `klFun`-based terms. -/
noncomputable def klFunList : List ℝ → List ℝ → List ℝ
  | [], _ => []
  | _ :: _, [] => []
  | p :: ps, q :: qs => (q * klFun (p / q)) :: klFunList ps qs

noncomputable def klDivKLFunList (ps qs : List ℝ) : ℝ :=
  HeytingLean.Math.ProbVec.sumList (klFunList ps qs)

/-- Nonnegativity of the `klFun`-based KL representation. -/
private lemma klDivKLFunList_nonneg
    (ps qs : List ℝ)
    (hp_nonneg : ∀ x ∈ ps, 0 ≤ x)
    (hq_pos    : ∀ x ∈ qs, 0 < x)
    (hlen      : ps.length = qs.length) :
    0 ≤ klDivKLFunList ps qs := by
  classical
  revert qs hp_nonneg hq_pos hlen
  induction ps with
  | nil =>
      intro qs hp_nonneg hq_pos hlen
      cases qs with
      | nil =>
          simp [klDivKLFunList, klFunList,
                HeytingLean.Math.ProbVec.sumList]
      | cons q qs =>
          cases hlen
  | cons p ps ih =>
      intro qs hp_nonneg hq_pos hlen
      cases qs with
      | nil =>
          cases hlen
      | cons q qs =>
          have hp_head : 0 ≤ p := hp_nonneg _ (by simp)
          have hq_head : 0 < q := hq_pos _ (by simp)
          have hp_tl : ∀ x ∈ ps, 0 ≤ x := by
            intro x hx; exact hp_nonneg _ (by simp [hx])
          have hq_tl : ∀ x ∈ qs, 0 < x := by
            intro x hx; exact hq_pos _ (by simp [hx])
          have h_tl_len : ps.length = qs.length := by
            simpa using congrArg Nat.pred hlen
          have h_tail_nonneg :
              0 ≤ klDivKLFunList ps qs :=
            ih qs hp_tl hq_tl h_tl_len
          have h_div_nonneg : 0 ≤ p / q :=
            div_nonneg hp_head (le_of_lt hq_head)
          have h_kl_nonneg : 0 ≤ klFun (p / q) :=
            klFun_nonneg h_div_nonneg
          have hq_nonneg : 0 ≤ q := le_of_lt hq_head
          have h_head_nonneg :
              0 ≤ q * klFun (p / q) :=
            mul_nonneg hq_nonneg h_kl_nonneg
          -- Combine head and tail contributions.
          have :
              0 ≤ q * klFun (p / q) + klDivKLFunList ps qs :=
            add_nonneg h_head_nonneg h_tail_nonneg
          simpa [klDivKLFunList, klFunList,
                 HeytingLean.Math.ProbVec.sumList] using this

/-- Express discrete KL as a sum of `qᵢ * klFun (pᵢ / qᵢ)` terms plus a
linear correction, under list-level probability assumptions. -/
private lemma klDivL_eq_klDivKLFunList_sub_sumDiff_aux :
    ∀ (ps qs : List ℝ),
      (∀ x ∈ ps, 0 ≤ x) →
      (∀ x ∈ qs, 0 < x) →
      ps.length = qs.length →
      klDivL ps qs =
        klDivKLFunList ps qs -
          (HeytingLean.Math.ProbVec.sumList qs -
            HeytingLean.Math.ProbVec.sumList ps)
  | [], [], _, _, _ => by
      simp [klDivL, klDivKLFunList, klFunList,
            HeytingLean.Math.ProbVec.sumList]
  | p :: ps, q :: qs, hp_nonneg, hq_pos, hlen => by
      have hp_head : 0 ≤ p := hp_nonneg _ (by simp)
      have hq_head : 0 < q := hq_pos _ (by simp)
      have hp_tl : ∀ x ∈ ps, 0 ≤ x := by
        intro x hx; exact hp_nonneg _ (by simp [hx])
      have hq_tl : ∀ x ∈ qs, 0 < x := by
        intro x hx; exact hq_pos _ (by simp [hx])
      have h_tl_len : ps.length = qs.length := by
        simpa using congrArg Nat.pred hlen
      have h_tail :
          klDivL ps qs =
            klDivKLFunList ps qs -
              (HeytingLean.Math.ProbVec.sumList qs -
                HeytingLean.Math.ProbVec.sumList ps) :=
        klDivL_eq_klDivKLFunList_sub_sumDiff_aux
          ps qs hp_tl hq_tl h_tl_len
      have h_head :
          klTerm p q = q * klFun (p / q) - (q - p) :=
        klTerm_eq_q_mul_klFun_sub p q hp_head hq_head
      calc
        klDivL (p :: ps) (q :: qs)
            = klTerm p q + klDivL ps qs := by
                simp [klDivL]
        _ = (q * klFun (p / q) - (q - p)) +
              (klDivKLFunList ps qs -
                (HeytingLean.Math.ProbVec.sumList qs -
                  HeytingLean.Math.ProbVec.sumList ps)) := by
                simp [h_head, h_tail]
        _ = klDivKLFunList (p :: ps) (q :: qs) -
              (HeytingLean.Math.ProbVec.sumList (q :: qs) -
                HeytingLean.Math.ProbVec.sumList (p :: ps)) := by
                simp [klDivKLFunList, klFunList,
                      HeytingLean.Math.ProbVec.sumList,
                      sub_eq_add_neg, add_comm, add_left_comm,
                      add_assoc]
  | [], _ :: _, _, _, hlen => by cases hlen
  | _ :: _, [], _, _, hlen => by cases hlen

/-! ### List- and array-level KL nonnegativity under probability assumptions -/

private lemma klDivL_ge_lowerBoundRec_aux :
    ∀ (ps qs : List ℝ),
      (∀ x ∈ ps, 0 ≤ x) →
      (∀ x ∈ qs, 0 < x) →
      ps.length = qs.length →
      klDivL ps qs ≥ lowerBoundRec ps qs
  | [], [], _, _, _ => by simp [klDivL, lowerBoundRec]
  | p :: ps, q :: qs, hp_nonneg, hq_pos, hlen => by
      have hp_head : 0 ≤ p := hp_nonneg _ (by simp)
      have hq_head : 0 < q := hq_pos _ (by simp)
      have h_tl_len : ps.length = qs.length := by
        simpa using congrArg Nat.pred hlen
      have hp_tl : ∀ x ∈ ps, 0 ≤ x := by
        intro x hx
        exact hp_nonneg _ (by simp [hx])
      have hq_tl : ∀ x ∈ qs, 0 < x := by
        intro x hx
        exact hq_pos _ (by simp [hx])
      have h_head_bound :
          klTerm p q ≥ (if 0 < p then p - q else 0) :=
        klTerm_ge_if_pos_sub p q hp_head hq_head
      have h_tail_bound :
          klDivL ps qs ≥ lowerBoundRec ps qs :=
        klDivL_ge_lowerBoundRec_aux ps qs hp_tl hq_tl h_tl_len
      have h_add :
          klTerm p q + klDivL ps qs ≥
            (if 0 < p then p - q else 0) + lowerBoundRec ps qs :=
        add_le_add h_head_bound h_tail_bound
      simpa [klDivL, lowerBoundRec] using h_add
  | [], _ :: _, _ , _, hlen => by cases hlen
  | _ :: _, [], _ , _, hlen => by cases hlen

lemma klDivL_ge_lowerBoundRec
    (ps qs : List ℝ)
    (hp_nonneg : ∀ x ∈ ps, 0 ≤ x)
    (hq_pos    : ∀ x ∈ qs, 0 < x)
    (hlen      : ps.length = qs.length) :
    klDivL ps qs ≥ lowerBoundRec ps qs :=
  klDivL_ge_lowerBoundRec_aux ps qs hp_nonneg hq_pos hlen

lemma lowerBoundRec_ge_sumDiff :
    ∀ (ps qs : List ℝ),
      (∀ x ∈ ps, 0 ≤ x) →
      (∀ x ∈ qs, 0 < x) →
      ps.length = qs.length →
      lowerBoundRec ps qs ≥
        HeytingLean.Math.ProbVec.sumList ps -
          HeytingLean.Math.ProbVec.sumList qs
  | [], [], _ , _, _ => by
      simp [lowerBoundRec, HeytingLean.Math.ProbVec.sumList]
  | p :: ps, q :: qs, hp_nonneg, hq_pos, hlen => by
      have hp_head : 0 ≤ p := hp_nonneg _ (by simp)
      have hq_head : 0 < q := hq_pos _ (by simp)
      have hp_tl : ∀ x ∈ ps, 0 ≤ x := by
        intro x hx; exact hp_nonneg _ (by simp [hx])
      have hq_tl : ∀ x ∈ qs, 0 < x := by
        intro x hx; exact hq_pos _ (by simp [hx])
      have h_tl_len : ps.length = qs.length := by
        simpa using congrArg Nat.pred hlen
      have h_tail :
          lowerBoundRec ps qs ≥
            HeytingLean.Math.ProbVec.sumList ps -
              HeytingLean.Math.ProbVec.sumList qs :=
        lowerBoundRec_ge_sumDiff ps qs hp_tl hq_tl h_tl_len
      -- Per-head lower bound `if 0 < p then p - q else 0 ≥ p - q`.
      have h_head :
          (if 0 < p then p - q else 0) ≥ p - q := by
        by_cases hp_pos : 0 < p
        · -- Positive case: both sides are `p - q`.
          simp [hp_pos]
        · -- Here `p ≤ 0`, but also `0 ≤ p`, so `p = 0`.
          have hp_le : p ≤ 0 := le_of_not_gt hp_pos
          have hp_eq : p = 0 := le_antisymm hp_le hp_head
          have hq_nonneg : 0 ≤ q := le_of_lt hq_head
          have h_le0 : p - q ≤ 0 := by
            simp [hp_eq, sub_eq_add_neg, hq_nonneg]
          have : 0 ≥ p - q := h_le0
          simpa [hp_pos] using this
      have h_add :
          (if 0 < p then p - q else 0) + lowerBoundRec ps qs ≥
            (p - q) +
              (HeytingLean.Math.ProbVec.sumList ps -
                HeytingLean.Math.ProbVec.sumList qs) :=
        add_le_add h_head h_tail
      -- Re-express both sides in terms of `lowerBoundRec` and list sums.
      simpa [lowerBoundRec, HeytingLean.Math.ProbVec.sumList,
             sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_add
  | [], _ :: _, _, _, hlen => by cases hlen
  | _ :: _, [], _, _, hlen => by cases hlen

/-- Bundled probability-style assumptions for discrete KL on lists. -/
structure KLAssumptions (ps qs : List ℝ) : Prop where
  nonneg_p : ∀ x ∈ ps, 0 ≤ x
  pos_q    : ∀ x ∈ qs, 0 < x
  len_eq   : ps.length = qs.length
  sum_p1   : HeytingLean.Math.ProbVec.sumList ps = 1
  sum_q1   : HeytingLean.Math.ProbVec.sumList qs = 1

/-- General Gibbs-style nonnegativity for discrete KL under
probability-style assumptions: for list-valued probability vectors
`ps`, `qs` (nonnegative entries summing to `1`, and with strictly
positive support for `qs`), the guarded KL divergence
`klDivL ps qs` is nonnegative. -/
lemma klDivL_nonneg
    (ps qs : List ℝ) (h : KLAssumptions ps qs) :
    0 ≤ klDivL ps qs := by
  rcases h with ⟨hp_nonneg, hq_pos, hlen, hp_sum1, hq_sum1⟩
  have h_le_diff :
      HeytingLean.Math.ProbVec.sumList ps -
        HeytingLean.Math.ProbVec.sumList qs ≤
        klDivL ps qs := by
    -- `klDivL ≥ lowerBoundRec ≥ diff` gives `diff ≤ klDivL`.
    have h1 : klDivL ps qs ≥ lowerBoundRec ps qs :=
      klDivL_ge_lowerBoundRec ps qs hp_nonneg hq_pos hlen
    have h2 :
        lowerBoundRec ps qs ≥
          HeytingLean.Math.ProbVec.sumList ps -
            HeytingLean.Math.ProbVec.sumList qs :=
      lowerBoundRec_ge_sumDiff ps qs hp_nonneg hq_pos hlen
    have h1' : lowerBoundRec ps qs ≤ klDivL ps qs := h1
    have h2' :
        HeytingLean.Math.ProbVec.sumList ps -
          HeytingLean.Math.ProbVec.sumList qs ≤
          lowerBoundRec ps qs := h2
    exact le_trans h2' h1'
  have h_diff_zero :
      HeytingLean.Math.ProbVec.sumList ps -
        HeytingLean.Math.ProbVec.sumList qs = 0 := by
    simpa [hp_sum1, hq_sum1, sub_eq_add_neg]
  have : 0 ≤ klDivL ps qs := by
    -- Rewrite the diff on the left as `0`.
    simpa [h_diff_zero] using h_le_diff
  simpa using this

/-- Array-level version of `klDivL_nonneg`, phrased via explicit
assumptions on the corresponding lists. -/
lemma klDivR_nonneg
    (p q : Array ℝ)
    (hp_nonneg : ∀ x ∈ p.toList, 0 ≤ x)
    (hq_pos   : ∀ x ∈ q.toList, 0 < x)
    (hlen     : p.toList.length = q.toList.length)
    (hp_sum1  : HeytingLean.Math.ProbVec.sumList p.toList = 1)
    (hq_sum1  : HeytingLean.Math.ProbVec.sumList q.toList = 1) :
    0 ≤ klDivR p q := by
  -- Package the list-level assumptions into `KLAssumptions` and reuse the
  -- core Gibbs-style inequality.
  let hAssump : KLAssumptions p.toList q.toList :=
    { nonneg_p := hp_nonneg
      pos_q    := hq_pos
      len_eq   := hlen
      sum_p1   := hp_sum1
      sum_q1   := hq_sum1 }
  have h :
      0 ≤ klDivL p.toList q.toList :=
    klDivL_nonneg p.toList q.toList hAssump
  simpa [klDivR] using h

/-- Under `KLAssumptions`, discrete KL admits a `klFun`-based
representation with no residual linear term: the mass-preservation
constraints ensure that the affine correction cancels. -/
lemma klDivL_eq_klDivKLFunList
    (ps qs : List ℝ) (h : KLAssumptions ps qs) :
    klDivL ps qs = klDivKLFunList ps qs := by
  rcases h with ⟨hp_nonneg, hq_pos, hlen, hp_sum1, hq_sum1⟩
  have h_eq :
      klDivL ps qs =
        klDivKLFunList ps qs -
          (HeytingLean.Math.ProbVec.sumList qs -
            HeytingLean.Math.ProbVec.sumList ps) :=
    klDivL_eq_klDivKLFunList_sub_sumDiff_aux
      ps qs hp_nonneg hq_pos hlen
  have h_diff_zero :
      HeytingLean.Math.ProbVec.sumList qs -
        HeytingLean.Math.ProbVec.sumList ps = 0 := by
    simpa [hp_sum1, hq_sum1, sub_eq_add_neg]
  simpa [h_diff_zero] using h_eq

/-- Auxiliary lemma: if the `klFun`-based discrete KL representation
vanishes under the usual probability assumptions, then the underlying
probability lists coincide. -/
private lemma eq_of_klDivKLFunList_eq_zero_aux :
    ∀ (ps qs : List ℝ),
      (∀ x ∈ ps, 0 ≤ x) →
      (∀ x ∈ qs, 0 < x) →
      ps.length = qs.length →
      klDivKLFunList ps qs = 0 →
      ps = qs
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hlen, _ => by cases hlen
  | _ :: _, [], _, _, hlen, _ => by cases hlen
  | p :: ps, q :: qs, hp_nonneg, hq_pos, hlen, h_zero => by
      classical
      have hp_head : 0 ≤ p := hp_nonneg _ (by simp)
      have hq_head : 0 < q := hq_pos _ (by simp)
      have hp_tl : ∀ x ∈ ps, 0 ≤ x := by
        intro x hx; exact hp_nonneg _ (by simp [hx])
      have hq_tl : ∀ x ∈ qs, 0 < x := by
        intro x hx; exact hq_pos _ (by simp [hx])
      have h_tl_len : ps.length = qs.length := by
        simpa using congrArg Nat.pred hlen
      have h_decomp :
          klDivKLFunList (p :: ps) (q :: qs) =
            q * klFun (p / q) + klDivKLFunList ps qs := by
        simp [klDivKLFunList, klFunList,
              HeytingLean.Math.ProbVec.sumList]
      have h_sum_zero :
          q * klFun (p / q) + klDivKLFunList ps qs = 0 := by
        simpa [h_decomp] using h_zero
      -- Nonnegativity of head and tail contributions.
      have h_head_nonneg : 0 ≤ q * klFun (p / q) := by
        have h_div_nonneg : 0 ≤ p / q :=
          div_nonneg hp_head (le_of_lt hq_head)
        have h_kl : 0 ≤ klFun (p / q) :=
          klFun_nonneg h_div_nonneg
        have hq_nonneg : 0 ≤ q := le_of_lt hq_head
        exact mul_nonneg hq_nonneg h_kl
      have h_tail_nonneg :
          0 ≤ klDivKLFunList ps qs :=
        klDivKLFunList_nonneg ps qs hp_tl hq_tl h_tl_len
      -- Extract that both terms are individually zero.
      have h_head_le_zero :
          q * klFun (p / q) ≤ 0 := by
        have :
            q * klFun (p / q) ≤
              q * klFun (p / q) + klDivKLFunList ps qs :=
          le_add_of_nonneg_right h_tail_nonneg
        simpa [h_sum_zero] using this
      have h_tail_le_zero :
          klDivKLFunList ps qs ≤ 0 := by
        have :
            klDivKLFunList ps qs ≤
              q * klFun (p / q) + klDivKLFunList ps qs :=
          le_add_of_nonneg_left h_head_nonneg
        simpa [h_sum_zero] using this
      have h_head_zero :
          q * klFun (p / q) = 0 :=
        le_antisymm h_head_le_zero h_head_nonneg
      have h_tail_zero :
          klDivKLFunList ps qs = 0 :=
        le_antisymm h_tail_le_zero h_tail_nonneg
      -- From `q * klFun (p/q) = 0` and `q > 0`, deduce `p = q`.
      have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_head
      have h_kl_zero :
          klFun (p / q) = 0 := by
        have := mul_eq_zero.mp h_head_zero
        exact this.resolve_left hq_ne
      have h_div_nonneg : 0 ≤ p / q :=
        div_nonneg hp_head (le_of_lt hq_head)
      have h_ratio :
          p / q = 1 :=
        (klFun_eq_zero_iff h_div_nonneg).mp h_kl_zero
      have h_mul :
          q * (p / q) = q := by
        simpa [h_ratio, one_mul] using
          congrArg (fun t => q * t) h_ratio
      have hqp :
          q * (p / q) = p := by
        field_simp [div_eq_mul_inv, hq_ne]
      have hpq : p = q := by
        simpa [hqp] using h_mul
      -- Recurse on the tail lists.
      have h_tail_eq :
          ps = qs :=
        eq_of_klDivKLFunList_eq_zero_aux ps qs
          hp_tl hq_tl h_tl_len h_tail_zero
      simp [hpq, h_tail_eq]

/-- Equality characterisation for discrete KL on lists: under
`KLAssumptions`, the guarded discrete KL is zero if and only if the
probability vectors coincide. -/
lemma klDivL_eq_zero_iff_eq
    (ps qs : List ℝ) (h : KLAssumptions ps qs) :
    klDivL ps qs = 0 ↔ ps = qs := by
  classical
  rcases h with ⟨hp_nonneg, hq_pos, hlen, hp_sum1, hq_sum1⟩
  constructor
  · intro h0
    have h_repr :
        klDivL ps qs = klDivKLFunList ps qs :=
      klDivL_eq_klDivKLFunList ps qs
        ⟨hp_nonneg, hq_pos, hlen, hp_sum1, hq_sum1⟩
    have h_fun_zero :
        klDivKLFunList ps qs = 0 := by
      have := congrArg id h0
      simpa [h_repr] using this
    exact
      eq_of_klDivKLFunList_eq_zero_aux ps qs
        hp_nonneg hq_pos hlen h_fun_zero
  · intro h_eq
    subst h_eq
    simp [klDivL_self_zero]

/-- Array-level version of the KL uniqueness lemma: under explicit
probability assumptions on the underlying lists, `klDivR p q = 0`
forces `p = q`. -/
lemma klDivR_eq_zero_iff_eq
    (p q : Array ℝ)
    (hp_nonneg : ∀ x ∈ p.toList, 0 ≤ x)
    (hq_pos   : ∀ x ∈ q.toList, 0 < x)
    (hlen     : p.toList.length = q.toList.length)
    (hp_sum1  : HeytingLean.Math.ProbVec.sumList p.toList = 1)
    (hq_sum1  : HeytingLean.Math.ProbVec.sumList q.toList = 1) :
    klDivR p q = 0 ↔ p = q := by
  classical
  let hAssump : KLAssumptions p.toList q.toList :=
    { nonneg_p := hp_nonneg
      pos_q    := hq_pos
      len_eq   := hlen
      sum_p1   := hp_sum1
      sum_q1   := hq_sum1 }
  have h_list :
      klDivL p.toList q.toList = 0 ↔
        p.toList = q.toList :=
    klDivL_eq_zero_iff_eq p.toList q.toList hAssump
  constructor
  · intro h0
    have h0_list :
        klDivL p.toList q.toList = 0 := by
      simpa [klDivR] using h0
    have h_eq_lists :
        p.toList = q.toList := (h_list.mp h0_list)
    have h_eq_arrays : p = q :=
      Array.ext' (by simpa using h_eq_lists)
    exact h_eq_arrays
  · intro h_eq
    subst h_eq
    simp [klDivR]

/-! Expected free energy scaffolds -/

structure EFEInputs where
  costs : Array ℝ      -- per-outcome cost (negative log-likelihood surrogate)
  post  : Array ℝ      -- posterior over outcomes
  prior : Array ℝ      -- prior over outcomes

def riskR (x : EFEInputs) : ℝ :=
  arrSum (arrZipWith (fun c p => c * p) x.costs x.post)

def igR (x : EFEInputs) : ℝ :=
  klDivR x.post x.prior

def efeR (x : EFEInputs) : ℝ := riskR x + igR x

lemma efe_eq_risk_add_ig (x : EFEInputs) : efeR x = riskR x + igR x := rfl

/-- If the information-gain term is nonnegative, then expected free energy
dominates the risk term, simply because `efeR = riskR + igR`. -/
lemma riskR_le_efeR_of_igR_nonneg (x : EFEInputs) (hig : 0 ≤ igR x) :
    riskR x ≤ efeR x := by
  -- From `0 ≤ igR x` we get `riskR x + 0 ≤ riskR x + igR x`.
  have h := add_le_add_left hig (riskR x)
  simpa [efeR] using h

/-- Diagonal information-gain nonnegativity: if `post = prior` as
arrays, then `igR x = KL(post ‖ post) ≥ 0` without requiring any
additional probability assumptions. -/
lemma igR_self_nonneg (x : EFEInputs) (h : x.post = x.prior) :
    0 ≤ igR x := by
  unfold igR
  -- rewrite the KL in terms of `post` only and use the diagonal lemma
  simpa [h] using klDivR_self_nonneg x.post

/-- On the diagonal, the information-gain term itself vanishes:
if `post = prior`, then the KL divergence is definitionally zero. -/
lemma igR_self_zero (x : EFEInputs) (h : x.post = x.prior) :
    igR x = 0 := by
  unfold igR
  simpa [h] using klDivR_self_zero x.post

/-- Under explicit probability assumptions on the posterior and prior
arrays, the information-gain term `igR` is nonnegative, by the
array-level Gibbs inequality for discrete KL. -/
lemma igR_nonneg
    (x : EFEInputs)
    (hp_nonneg : ∀ r ∈ x.post.toList, 0 ≤ r)
    (hq_pos    : ∀ r ∈ x.prior.toList, 0 < r)
    (hlen      : x.post.toList.length = x.prior.toList.length)
    (hp_sum1   : HeytingLean.Math.ProbVec.sumList x.post.toList = 1)
    (hq_sum1   : HeytingLean.Math.ProbVec.sumList x.prior.toList = 1) :
    0 ≤ igR x := by
  unfold igR
  exact
    klDivR_nonneg x.post x.prior
      hp_nonneg hq_pos hlen hp_sum1 hq_sum1

/-- A bundled “variational” lower bound: under the same explicit
probability assumptions used for the Gibbs inequality, expected free
energy dominates risk, with the gap exactly given by the nonnegative
information-gain term. -/
lemma efe_lower_bound
    (x : EFEInputs)
    (hp_nonneg : ∀ r ∈ x.post.toList, 0 ≤ r)
    (hq_pos    : ∀ r ∈ x.prior.toList, 0 < r)
    (hlen      : x.post.toList.length = x.prior.toList.length)
    (hp_sum1   : HeytingLean.Math.ProbVec.sumList x.post.toList = 1)
    (hq_sum1   : HeytingLean.Math.ProbVec.sumList x.prior.toList = 1) :
    riskR x ≤ efeR x := by
  have hig : 0 ≤ igR x :=
    igR_nonneg x hp_nonneg hq_pos hlen hp_sum1 hq_sum1
  exact riskR_le_efeR_of_igR_nonneg x hig

/-- If posterior and prior coincide for a given `EFEInputs`, then
expected free energy collapses to the risk term: there is no
information-gain gap.  Together with `efe_lower_bound`, this shows
that the lower bound is tight on the diagonal. -/
lemma efe_eq_risk_of_post_eq_prior (x : EFEInputs) (h : x.post = x.prior) :
    efeR x = riskR x := by
  have h0 : igR x = 0 := igR_self_zero x h
  -- Start from the definitional identity and specialise to `igR x = 0`.
  have := efe_eq_risk_add_ig x
  calc
    efeR x = riskR x + igR x := this
    _ = riskR x + 0 := by simp [h0]
    _ = riskR x := by simp

/-- For any `EFEInputs`, the gap between expected free energy and risk
is exactly the information-gain term.  This is the finite, discrete
analogue of the usual variational identity `F[q] = \mathbb{E}_q[L] +
KL(q \,\|\, p)`, specialised to our Real-valued scaffold. -/
lemma efe_sub_risk_eq_igR (x : EFEInputs) :
    efeR x - riskR x = igR x := by
  -- Expand `efeR` in terms of `riskR` and `igR` and simplify.
  have := efe_eq_risk_add_ig x
  -- Rearrange `efeR = riskR + igR` into `efeR - riskR = igR`.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using congrArg (fun t => t - riskR x) this

/-- Equivalence form of the variational identity: expected free energy
equals risk if and only if the information-gain term vanishes. -/
lemma efe_eq_risk_iff_igR_zero (x : EFEInputs) :
    efeR x = riskR x ↔ igR x = 0 := by
  constructor
  · intro h
    -- If `efeR = riskR` then the gap `efeR - riskR` is zero, hence so is `igR`.
    have hgap : efeR x - riskR x = 0 := by simpa [h]
    simpa [efe_sub_risk_eq_igR] using hgap
  · intro h0
    -- Conversely, if `igR = 0` then the gap vanishes and `efeR = riskR`.
    have hgap : efeR x - riskR x = 0 := by simpa [efe_sub_risk_eq_igR, h0]
    have := sub_eq_zero.mp hgap
    exact this

/-- Under explicit probability assumptions on posterior and prior,
the information-gain term vanishes if and only if the two discrete
distributions coincide. -/
lemma igR_zero_iff_post_eq_prior
    (x : EFEInputs)
    (hp_nonneg : ∀ r ∈ x.post.toList, 0 ≤ r)
    (hq_pos    : ∀ r ∈ x.prior.toList, 0 < r)
    (hlen      : x.post.toList.length = x.prior.toList.length)
    (hp_sum1   : HeytingLean.Math.ProbVec.sumList x.post.toList = 1)
    (hq_sum1   : HeytingLean.Math.ProbVec.sumList x.prior.toList = 1) :
    igR x = 0 ↔ x.post = x.prior := by
  have hArr :
      klDivR x.post x.prior = 0 ↔
        x.post = x.prior :=
    klDivR_eq_zero_iff_eq x.post x.prior
      hp_nonneg hq_pos hlen hp_sum1 hq_sum1
  simpa [igR] using hArr

/-- Equivalence form of the variational identity specialised to
probability-style assumptions: expected free energy equals risk if
and only if posterior and prior coincide. -/
lemma efe_eq_risk_iff_post_eq_prior
    (x : EFEInputs)
    (hp_nonneg : ∀ r ∈ x.post.toList, 0 ≤ r)
    (hq_pos    : ∀ r ∈ x.prior.toList, 0 < r)
    (hlen      : x.post.toList.length = x.prior.toList.length)
    (hp_sum1   : HeytingLean.Math.ProbVec.sumList x.post.toList = 1)
    (hq_sum1   : HeytingLean.Math.ProbVec.sumList x.prior.toList = 1) :
    efeR x = riskR x ↔ x.post = x.prior := by
  have h_eq_ig : efeR x = riskR x ↔ igR x = 0 :=
    efe_eq_risk_iff_igR_zero x
  have h_ig_zero :
      igR x = 0 ↔ x.post = x.prior :=
    igR_zero_iff_post_eq_prior x
      hp_nonneg hq_pos hlen hp_sum1 hq_sum1
  exact h_eq_ig.trans h_ig_zero

/-! Finite argmin witness on lists -/

def argminIdxAux : Nat → Nat → ℝ → List ℝ → Nat × ℝ
  | _, best, bestVal, []      => (best, bestVal)
  | i, best, bestVal, x :: xs =>
      if x < bestVal then argminIdxAux (i+1) i x xs
      else argminIdxAux (i+1) best bestVal xs

def argminIdx (xs : List ℝ) (default : ℝ := 0) : Nat × ℝ :=
  match xs with
  | []      => (0, default)
  | x :: xs => argminIdxAux 1 0 x xs

/-! For compile-only sanity; full minimality lemma can be added later if needed. -/

end
end ActiveInference
end Quantum
end HeytingLean
