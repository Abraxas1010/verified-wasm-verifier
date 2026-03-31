import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Epiplexity.Bounds
import HeytingLean.Epiplexity.Conditional
import HeytingLean.Epiplexity.Crypto.Axioms

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

namespace Factorization

/-!
Factorization / one-way permutation asymmetry (paper Theorem 13, Theorem 25, Corollary 26).

We work on finite spaces `BitStr n` and model the one-way-permutation hypothesis as an explicit
success-probability bound for *conditional samplers* `y ↦ Q(·|y)` (no universal machine model).

Key analytic ingredient: Jensen for `Real.log`, using Mathlib’s
`Real.strictConcaveOn_log_Ioi` + `ConcaveOn.le_map_sum`.
-/

noncomputable def Un (n : Nat) : FinDist (BitStr n) :=
  Epiplexity.FinDist.uniform (α := BitStr n)

/-! ### True joint distributions for a permutation `e` -/

/-- Joint distribution of `(X,Y)` with `X ~ U_n` and `Y = e X` (zeros off the graph). -/
noncomputable def jointXY {n : Nat} (e : BitStr n ≃ BitStr n) : FinDist (BitStr n × BitStr n) where
  pmf xy := if xy.2 = e xy.1 then 1 / (Fintype.card (BitStr n) : ℝ) else 0
  nonneg xy := by
    by_cases h : xy.2 = e xy.1 <;> simp [h]
  sum_one := by
    classical
    -- Sum over `x`, then over `y`; each inner sum has exactly one nonzero term.
    have hswap :
        (∑ xy : BitStr n × BitStr n,
            (if xy.2 = e xy.1 then 1 / (Fintype.card (BitStr n) : ℝ) else 0))
          =
        ∑ x : BitStr n, ∑ y : BitStr n,
          (if y = e x then 1 / (Fintype.card (BitStr n) : ℝ) else 0) := by
      simpa using (Fintype.sum_prod_type
        (fun xy : BitStr n × BitStr n =>
          (if xy.2 = e xy.1 then 1 / (Fintype.card (BitStr n) : ℝ) else 0)))
    calc
      (∑ xy : BitStr n × BitStr n,
          (if xy.2 = e xy.1 then 1 / (Fintype.card (BitStr n) : ℝ) else 0))
          = ∑ x : BitStr n, ∑ y : BitStr n,
              (if y = e x then 1 / (Fintype.card (BitStr n) : ℝ) else 0) := hswap
      _ = ∑ x : BitStr n, (1 / (Fintype.card (BitStr n) : ℝ)) := by
            simp
      _ = (Fintype.card (BitStr n) : ℝ) * (1 / (Fintype.card (BitStr n) : ℝ)) := by
            simp [Finset.sum_const]
      _ = 1 := by
            have hcard0 : (Fintype.card (BitStr n) : ℝ) ≠ 0 := by
              exact_mod_cast (ne_of_gt (Fintype.card_pos (α := BitStr n)))
            field_simp [hcard0]

/-- Joint distribution of `(Y,X)` with `X ~ U_n` and `Y = e X` (equivalently, `X = e.symm Y`). -/
noncomputable def jointYX {n : Nat} (e : BitStr n ≃ BitStr n) : FinDist (BitStr n × BitStr n) where
  pmf yx := if yx.2 = e.symm yx.1 then 1 / (Fintype.card (BitStr n) : ℝ) else 0
  nonneg yx := by
    by_cases h : yx.2 = e.symm yx.1 <;> simp [h]
  sum_one := by
    classical
    have hswap :
        (∑ yx : BitStr n × BitStr n,
            (if yx.2 = e.symm yx.1 then 1 / (Fintype.card (BitStr n) : ℝ) else 0))
          =
        ∑ y : BitStr n, ∑ x : BitStr n,
          (if x = e.symm y then 1 / (Fintype.card (BitStr n) : ℝ) else 0) := by
      simpa using (Fintype.sum_prod_type
        (fun yx : BitStr n × BitStr n =>
          (if yx.2 = e.symm yx.1 then 1 / (Fintype.card (BitStr n) : ℝ) else 0)))
    calc
      (∑ yx : BitStr n × BitStr n,
          (if yx.2 = e.symm yx.1 then 1 / (Fintype.card (BitStr n) : ℝ) else 0))
          = ∑ y : BitStr n, ∑ x : BitStr n,
              (if x = e.symm y then 1 / (Fintype.card (BitStr n) : ℝ) else 0) := hswap
      _ = ∑ y : BitStr n, (1 / (Fintype.card (BitStr n) : ℝ)) := by
            simp
      _ = (Fintype.card (BitStr n) : ℝ) * (1 / (Fintype.card (BitStr n) : ℝ)) := by
            simp [Finset.sum_const]
      _ = 1 := by
            have hcard0 : (Fintype.card (BitStr n) : ℝ) ≠ 0 := by
              exact_mod_cast (ne_of_gt (Fintype.card_pos (α := BitStr n)))
            field_simp [hcard0]

/-! ### A full-support “almost deterministic” forward conditional model -/

/-- Conditional distribution giving mass `1/2` to the correct output `e x`. -/
noncomputable def forwardCondDist {n : Nat} (hn : 0 < n) (e : BitStr n ≃ BitStr n) (x : BitStr n) :
    FinDist (BitStr n) where
  pmf y :=
    if y = e x then (1 / 2 : ℝ)
    else (1 / 2 : ℝ) / ((Fintype.card (BitStr n) : ℝ) - 1)
  nonneg y := by
    by_cases h : y = e x
    · simp [h]
    · have hcard_pos : (1 : ℝ) < (Fintype.card (BitStr n) : ℝ) := by
        have : 2 ≤ Fintype.card (BitStr n) := by
          -- `card(BitStr n) = 2^n ≥ 2` for `n>0`.
          have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
          have : 2 ≤ 2 ^ n := Nat.succ_le_iff.2 (Nat.one_lt_pow hn0 (by decide : 1 < 2))
          simpa [BitStr] using this
        exact_mod_cast this
      have hden_pos : 0 < (Fintype.card (BitStr n) : ℝ) - 1 := sub_pos.2 hcard_pos
      have : 0 ≤ (1 / 2 : ℝ) / ((Fintype.card (BitStr n) : ℝ) - 1) :=
        le_of_lt (div_pos (by norm_num) hden_pos)
      simpa [h] using this
  sum_one := by
    classical
    have hcard_pos : (1 : ℝ) < (Fintype.card (BitStr n) : ℝ) := by
      have : 2 ≤ Fintype.card (BitStr n) := by
        have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
        have : 2 ≤ 2 ^ n := Nat.succ_le_iff.2 (Nat.one_lt_pow hn0 (by decide : 1 < 2))
        simpa [BitStr] using this
      exact_mod_cast this
    have hden_ne0 : (Fintype.card (BitStr n) : ℝ) - 1 ≠ 0 :=
      ne_of_gt (sub_pos.2 hcard_pos)
    let y0 : BitStr n := e x
    let b : ℝ := (1 / 2 : ℝ) / ((Fintype.card (BitStr n) : ℝ) - 1)
    have hsplit :
        (∑ y : BitStr n, (if y = y0 then (1 / 2 : ℝ) else b))
          =
        (1 / 2 : ℝ) + ∑ y ∈ ({y0}ᶜ : Finset (BitStr n)), (if y = y0 then (1 / 2 : ℝ) else b) := by
      simpa using (Fintype.sum_eq_add_sum_compl y0 (fun y : BitStr n => if y = y0 then (1 / 2 : ℝ) else b))
    have hcomp :
        (∑ y ∈ ({y0}ᶜ : Finset (BitStr n)), (if y = y0 then (1 / 2 : ℝ) else b))
          =
        (∑ _y ∈ ({y0}ᶜ : Finset (BitStr n)), b) := by
      refine Finset.sum_congr rfl ?_
      intro y hy
      have hy0 : y ≠ y0 := by
        have : y ∉ ({y0} : Finset (BitStr n)) := by
          simpa using hy
        simpa using this
      simp [hy0]
    have hconst :
        (∑ _y ∈ ({y0}ᶜ : Finset (BitStr n)), b)
          =
        ((Fintype.card (BitStr n) : ℝ) - 1) * b := by
      simp [Finset.sum_const, Finset.card_compl]
    have hmul : ((Fintype.card (BitStr n) : ℝ) - 1) * b = (1 / 2 : ℝ) := by
      dsimp [b]
      field_simp [hden_ne0]
    have hsum :
        (∑ y : BitStr n,
            (if y = y0 then (1 / 2 : ℝ)
             else (1 / 2 : ℝ) / ((Fintype.card (BitStr n) : ℝ) - 1)))
          = 1 := by
      calc
        (∑ y : BitStr n,
            (if y = y0 then (1 / 2 : ℝ)
             else (1 / 2 : ℝ) / ((Fintype.card (BitStr n) : ℝ) - 1)))
            = (∑ y : BitStr n, if y = y0 then (1 / 2 : ℝ) else b) := by
                simp [b]
        _ = (1 / 2 : ℝ) +
              ∑ y ∈ ({y0}ᶜ : Finset (BitStr n)), (if y = y0 then (1 / 2 : ℝ) else b) := hsplit
        _ = (1 / 2 : ℝ) + ∑ _y ∈ ({y0}ᶜ : Finset (BitStr n)), b := by
              rw [hcomp]
        _ = (1 / 2 : ℝ) + ((Fintype.card (BitStr n) : ℝ) - 1) * b := by
              rw [hconst]
        _ = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
              rw [hmul]
        _ = 1 := by norm_num
    simpa [y0] using hsum

theorem forwardCondDist_Pos {n : Nat} (hn : 0 < n) (e : BitStr n ≃ BitStr n) (x y : BitStr n) :
    0 < (forwardCondDist (n := n) hn e x).pmf y := by
  classical
  by_cases h : y = e x
  · subst h
    simp [forwardCondDist]
  · have hcard_pos : (1 : ℝ) < (Fintype.card (BitStr n) : ℝ) := by
      have : 2 ≤ Fintype.card (BitStr n) := by
        have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
        have : 2 ≤ 2 ^ n := Nat.succ_le_iff.2 (Nat.one_lt_pow hn0 (by decide : 1 < 2))
        simpa [BitStr] using this
      exact_mod_cast this
    have hden_pos : 0 < (Fintype.card (BitStr n) : ℝ) - 1 := sub_pos.2 hcard_pos
    have : 0 < (1 / 2 : ℝ) / ((Fintype.card (BitStr n) : ℝ) - 1) :=
      div_pos (by norm_num) hden_pos
    simpa [forwardCondDist, h] using this

/-- A constant-size feasible conditional program for the forward direction (`Y|X`). -/
noncomputable def forwardCondProg {n : Nat} (hn : 0 < n) (e : BitStr n ≃ BitStr n) :
    CondProg (BitStr n) (BitStr n) where
  code := [true]
  runtime := 0
  dist := forwardCondDist (n := n) hn e
  distPos x y := forwardCondDist_Pos (n := n) hn e x y

@[simp] theorem forwardCondProg_codeLen {n : Nat} (hn : 0 < n) (e : BitStr n ≃ BitStr n) :
    (forwardCondProg (n := n) hn e).codeLen = 1 := by
  simp [forwardCondProg, CondProg.codeLen, HeytingLean.Meta.AIT.codeLength, HeytingLean.Meta.AIT.Program.length]

theorem nllBits_forwardCondDist_hit {n : Nat} (hn : 0 < n) (e : BitStr n ≃ BitStr n) (x : BitStr n) :
    Info.nllBits (forwardCondDist (n := n) hn e x) (e x) = 1 := by
  have hpos : 0 < (forwardCondDist (n := n) hn e x).pmf (e x) :=
    forwardCondDist_Pos (n := n) hn e x (e x)
  have hsafelog :
      InfoTheory.safeLog ((forwardCondDist (n := n) hn e x).pmf (e x))
        = Real.log ((forwardCondDist (n := n) hn e x).pmf (e x)) :=
    InfoTheory.safeLog_of_pos hpos
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
  -- The pmf at the "hit" is exactly `1/2`.
  have hpmf : (forwardCondDist (n := n) hn e x).pmf (e x) = (1 / 2 : ℝ) := by
    simp [forwardCondDist]
  -- Compute `-log₂(1/2)=1`.
  unfold Info.nllBits Info.nllNat
  simp [hpmf, one_div, Real.log_inv, hlog2_ne0]

theorem condCrossEntropyBits_jointXY_forward {n : Nat} (hn : 0 < n) (e : BitStr n ≃ BitStr n) :
    condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointXY (n := n) e)
        (forwardCondDist (n := n) hn e)
      = 1 := by
  classical
  unfold condCrossEntropyBits condNllBits
  -- Expand over `x,y` and use that only the graph points contribute.
  have hswap :
      (∑ xy : BitStr n × BitStr n,
          (jointXY (n := n) e).pmf xy * Info.nllBits (forwardCondDist (n := n) hn e xy.1) xy.2)
        =
      ∑ x : BitStr n, ∑ y : BitStr n,
        (jointXY (n := n) e).pmf (x, y) * Info.nllBits (forwardCondDist (n := n) hn e x) y := by
    simpa using (Fintype.sum_prod_type
      (fun xy : BitStr n × BitStr n =>
        (jointXY (n := n) e).pmf xy * Info.nllBits (forwardCondDist (n := n) hn e xy.1) xy.2))
  rw [hswap]
  -- Inner sum: only `y = e x` survives.
  have hinner :
      ∀ x : BitStr n,
        (∑ y : BitStr n,
            (jointXY (n := n) e).pmf (x, y) * Info.nllBits (forwardCondDist (n := n) hn e x) y)
          = (1 / (Fintype.card (BitStr n) : ℝ)) * 1 := by
    intro x
    have hs :
        (∑ y : BitStr n,
            (jointXY (n := n) e).pmf (x, y) * Info.nllBits (forwardCondDist (n := n) hn e x) y)
          =
        (jointXY (n := n) e).pmf (x, e x) *
          Info.nllBits (forwardCondDist (n := n) hn e x) (e x) := by
      classical
      refine Fintype.sum_eq_single (e x)
        (f := fun y : BitStr n =>
          (jointXY (n := n) e).pmf (x, y) * Info.nllBits (forwardCondDist (n := n) hn e x) y) ?_
      intro y hy
      have hpmf0 : (jointXY (n := n) e).pmf (x, y) = 0 := by
        simp [jointXY, hy]
      simp [hpmf0]
    rw [hs]
    have hpmf : (jointXY (n := n) e).pmf (x, e x) = 1 / (Fintype.card (BitStr n) : ℝ) := by
      simp [jointXY]
    simp [hpmf, nllBits_forwardCondDist_hit (n := n) hn e x]
  -- The outer sum is `card * (1/card) = 1`.
  calc
    (∑ x : BitStr n, ∑ y : BitStr n,
        (jointXY (n := n) e).pmf (x, y) * Info.nllBits (forwardCondDist (n := n) hn e x) y)
        = ∑ x : BitStr n, (1 / (Fintype.card (BitStr n) : ℝ)) * 1 := by
            simp [hinner]
    _ = (Fintype.card (BitStr n) : ℝ) * ((1 / (Fintype.card (BitStr n) : ℝ)) * 1) := by
          simp [Finset.sum_const]
    _ = 1 := by
          have hcard0 : (Fintype.card (BitStr n) : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (Fintype.card_pos (α := BitStr n)))
          field_simp [hcard0]

theorem HT_Y_given_X_le_two {n T : Nat} (hn : 0 < n) (e : BitStr n ≃ BitStr n)
    (opt : OptimalCondProg (α := BitStr n) (β := BitStr n) T (jointXY (n := n) e)) :
    opt.HT ≤ 2 := by
  -- Compare the MDL-optimal conditional program to the constant witness `forwardCondProg`.
  have hFeas : CondProg.Feasible T (forwardCondProg (n := n) hn e) := by
    simp [forwardCondProg, CondProg.Feasible]
  have hopt :
      condMdlCost (α := BitStr n) (β := BitStr n) (jointXY (n := n) e) opt.P
        ≤ condMdlCost (α := BitStr n) (β := BitStr n) (jointXY (n := n) e)
            (forwardCondProg (n := n) hn e) :=
    opt.optimal _ hFeas
  have hlen_nonneg : (0 : ℝ) ≤ (opt.P.codeLen : ℝ) := by exact_mod_cast Nat.zero_le _
  have hcost_lhs :
      condMdlCost (α := BitStr n) (β := BitStr n) (jointXY (n := n) e) opt.P
        = (opt.P.codeLen : ℝ) + opt.HT := by
    simp [condMdlCost, OptimalCondProg.HT]
  have hcost_rhs :
      condMdlCost (α := BitStr n) (β := BitStr n) (jointXY (n := n) e)
          (forwardCondProg (n := n) hn e)
        = 2 := by
    have hce :
        condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointXY (n := n) e)
            (forwardCondProg (n := n) hn e).dist
          = 1 := by
      simpa [forwardCondProg] using condCrossEntropyBits_jointXY_forward (n := n) hn e
    simp [condMdlCost, hce, forwardCondProg_codeLen (n := n) hn e]
    norm_num
  have hsum : (opt.P.codeLen : ℝ) + opt.HT ≤ 2 := by
    simpa [hcost_lhs, hcost_rhs] using hopt
  exact le_of_add_le_of_nonneg_right hsum hlen_nonneg

/-! ### One-wayness for conditional samplers (`X|Y`) -/

/-- Inversion success probability for a conditional sampler `Q(·|y)`, with `y` uniform. -/
noncomputable def invSuccess {n : Nat} (e : BitStr n ≃ BitStr n) (Q : BitStr n → FinDist (BitStr n)) :
    ℝ :=
  ∑ y : BitStr n, (Un n).pmf y * (Q y).pmf (e.symm y)

theorem invSuccess_pos {n : Nat} (e : BitStr n ≃ BitStr n) (Q : BitStr n → FinDist (BitStr n))
    (hQ : ∀ y, (Q y).Pos) :
    0 < invSuccess (n := n) e Q := by
  classical
  obtain ⟨y0⟩ := (inferInstance : Nonempty (BitStr n))
  have hw : 0 < (Un n).pmf y0 := by
    dsimp [Un]
    exact Epiplexity.FinDist.uniform_Pos (α := BitStr n) y0
  have hφ : 0 < (Q y0).pmf (e.symm y0) := hQ y0 (e.symm y0)
  have hterm : 0 < (Un n).pmf y0 * (Q y0).pmf (e.symm y0) := mul_pos hw hφ
  have hle :
      (Un n).pmf y0 * (Q y0).pmf (e.symm y0) ≤ invSuccess (n := n) e Q := by
    -- One term is bounded by the total sum.
    have hnonneg : ∀ y : BitStr n, 0 ≤ (Un n).pmf y * (Q y).pmf (e.symm y) := by
      intro y
      exact mul_nonneg ((Un n).nonneg y) ((Q y).nonneg (e.symm y))
    -- Use `single_le_sum`.
    simpa [invSuccess] using
      (Finset.single_le_sum (s := (Finset.univ : Finset (BitStr n)))
        (fun y _ => hnonneg y) (by simp))
  exact lt_of_lt_of_le hterm hle

theorem condCrossEntropyBits_jointYX_eq {n : Nat} (e : BitStr n ≃ BitStr n)
    (Q : BitStr n → FinDist (BitStr n)) :
    condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q
      =
    ∑ y : BitStr n, (Un n).pmf y * Info.nllBits (Q y) (e.symm y) := by
  classical
  unfold condCrossEntropyBits condNllBits
  -- Expand over `y,x`, then simplify the inner `x` sum using the definition of `jointYX`.
  have hswap :
      (∑ yx : BitStr n × BitStr n,
          (jointYX (n := n) e).pmf yx * Info.nllBits (Q yx.1) yx.2)
        =
      ∑ y : BitStr n, ∑ x : BitStr n,
          (jointYX (n := n) e).pmf (y, x) * Info.nllBits (Q y) x := by
    simpa using (Fintype.sum_prod_type
      (fun yx : BitStr n × BitStr n =>
        (jointYX (n := n) e).pmf yx * Info.nllBits (Q yx.1) yx.2))
  rw [hswap]
  -- For fixed `y`, only `x = e.symm y` contributes.
  have hinner :
      ∀ y : BitStr n,
        (∑ x : BitStr n,
            (jointYX (n := n) e).pmf (y, x) * Info.nllBits (Q y) x)
          = (Un n).pmf y * Info.nllBits (Q y) (e.symm y) := by
    intro y
    have hpmf : ∀ x : BitStr n,
        (jointYX (n := n) e).pmf (y, x) = if x = e.symm y then (Un n).pmf y else 0 := by
      intro x
      -- `jointYX` puts mass `1/card` on `x = e.symm y`, which equals `Un.pmf y`.
      by_cases hx : x = e.symm y
      · subst hx
        simp [jointYX, Un, Epiplexity.FinDist.uniform_pmf]
      · simp [jointYX, hx]
    classical
    simp [hpmf]
  -- Finish by rewriting `Un` and reassembling the outer sum.
  calc
    (∑ y : BitStr n, ∑ x : BitStr n, (jointYX (n := n) e).pmf (y, x) * Info.nllBits (Q y) x)
        = ∑ y : BitStr n, (Un n).pmf y * Info.nllBits (Q y) (e.symm y) := by
            simp [hinner]

/-- The Jensen lower bound in bits: `E[-log₂ p] ≥ log₂ (1 / E[p])`. -/
theorem condCrossEntropyBits_jointYX_ge_log2_invSuccess {n : Nat} (e : BitStr n ≃ BitStr n)
    (Q : BitStr n → FinDist (BitStr n)) (hQ : ∀ y, (Q y).Pos) :
    Epiplexity.log2 (1 / invSuccess (n := n) e Q) ≤
      condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q := by
  classical
  -- Jensen for concave `log` on the positive reals.
  let w : BitStr n → ℝ := fun y => (Un n).pmf y
  let p : BitStr n → ℝ := fun y => (Q y).pmf (e.symm y)
  have hw_nonneg : ∀ y, 0 ≤ w y := fun y => (Un n).nonneg y
  have hw_sum : (∑ y : BitStr n, w y) = 1 := by
    simp [w, Un]
  have hp_mem : ∀ y, p y ∈ Set.Ioi (0 : ℝ) := by
    intro y
    exact hQ y (e.symm y)
  have hjensen :
      (∑ y : BitStr n, w y * Real.log (p y)) ≤ Real.log (∑ y : BitStr n, w y * p y) := by
    have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
      (strictConcaveOn_log_Ioi).concaveOn
    have :=
      (ConcaveOn.le_map_sum (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ)) (f := Real.log)
        (t := (Finset.univ : Finset (BitStr n))) (w := w) (p := p)
        hconc (fun y _ => hw_nonneg y) (by simp [hw_sum]) (fun y _ => hp_mem y))
    simpa [smul_eq_mul, Finset.sum_attach] using this
  have hjensen' :
      (∑ y : BitStr n, w y * Real.log (p y)) ≤ Real.log (invSuccess (n := n) e Q) := by
    simpa [invSuccess, w, p] using hjensen
  -- Rewrite `condCrossEntropyBits` in terms of `log (p y)`.
  have hce :
      condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q
        = ∑ y : BitStr n, w y * ((-Real.log (p y)) / Real.log 2) := by
    have hce0 :
        condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q
          = ∑ y : BitStr n, w y * Info.nllBits (Q y) (e.symm y) := by
      simpa [w] using condCrossEntropyBits_jointYX_eq (n := n) e Q
    have hnll :
        ∀ y : BitStr n,
          Info.nllBits (Q y) (e.symm y) = (-Real.log (p y)) / Real.log 2 := by
      intro y
      have hpos : 0 < (Q y).pmf (e.symm y) := hQ y (e.symm y)
      have hsafelog :
          InfoTheory.safeLog ((Q y).pmf (e.symm y)) = Real.log ((Q y).pmf (e.symm y)) :=
        InfoTheory.safeLog_of_pos hpos
      unfold Info.nllBits Info.nllNat
      simp [p, hsafelog, div_eq_mul_inv]
    simp [hce0, hnll, w]
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hlog_inv :
      Real.log (1 / invSuccess (n := n) e Q) = -Real.log (invSuccess (n := n) e Q) := by
    simp [one_div, Real.log_inv]
  -- Negate Jensen and divide by `log 2 > 0`.
  have hneg :
      -Real.log (invSuccess (n := n) e Q) ≤ -∑ y : BitStr n, w y * Real.log (p y) := by
    simpa using (neg_le_neg hjensen')
  have hdiv :
      (-Real.log (invSuccess (n := n) e Q)) / Real.log 2 ≤
        (-∑ y : BitStr n, w y * Real.log (p y)) / Real.log 2 :=
    div_le_div_of_nonneg_right hneg (le_of_lt hlog2_pos)
  have hsum_rw :
      (-∑ y : BitStr n, w y * Real.log (p y)) / Real.log 2
        = ∑ y : BitStr n, w y * ((-Real.log (p y)) / Real.log 2) := by
    classical
    have hsum_mul :
        (∑ y : BitStr n, w y * Real.log (p y)) * (Real.log 2)⁻¹ =
          ∑ y : BitStr n, (w y * Real.log (p y)) * (Real.log 2)⁻¹ := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset (BitStr n)))
          (f := fun y => w y * Real.log (p y)) (a := (Real.log 2)⁻¹))
    calc
      (-∑ y : BitStr n, w y * Real.log (p y)) / Real.log 2
          = (-∑ y : BitStr n, w y * Real.log (p y)) * (Real.log 2)⁻¹ := by
              simp [div_eq_mul_inv]
      _ = -((∑ y : BitStr n, w y * Real.log (p y)) * (Real.log 2)⁻¹) := by ring
      _ = -(∑ y : BitStr n, (w y * Real.log (p y)) * (Real.log 2)⁻¹) := by
            simp [hsum_mul]
      _ = ∑ y : BitStr n, -((w y * Real.log (p y)) * (Real.log 2)⁻¹) := by
            simp
      _ = ∑ y : BitStr n, w y * ((-Real.log (p y)) / Real.log 2) := by
            apply Fintype.sum_congr
            intro y
            simp [div_eq_mul_inv]
            ring
  have :
      Real.log (1 / invSuccess (n := n) e Q) / Real.log 2 ≤
        ∑ y : BitStr n, w y * ((-Real.log (p y)) / Real.log 2) := by
    simpa [hlog_inv, hsum_rw] using hdiv
  -- Finish by rewriting to `log2` and `condCrossEntropyBits`.
  simpa [Epiplexity.log2, hce] using this

/-! ### Security predicate and theorems -/

/-- One-way permutation hypothesis (fixed `n`): all feasible conditional samplers have small inversion success. -/
def OWPSecure {n : Nat} (T : Nat) (e : BitStr n ≃ BitStr n) (ε : ℝ) : Prop :=
  ∀ A : CondProg (BitStr n) (BitStr n), CondProg.Feasible T A → invSuccess (n := n) e A.dist ≤ ε

theorem theorem25_core {n T : Nat} (hn : 9 ≤ n) (e : BitStr n ≃ BitStr n) (c : Nat)
    (hOWP : OWPSecure (n := n) T e (1 / ((n : ℝ) ^ (c + 1))))
    (optX : OptimalProg (α := BitStr n) T (Un n))
    (optY : OptimalProg (α := BitStr n) T (Un n))
    (optYgivenX : OptimalCondProg (α := BitStr n) (β := BitStr n) T (jointXY (n := n) e))
    (optXgivenY : OptimalCondProg (α := BitStr n) (β := BitStr n) T (jointYX (n := n) e)) :
    optXgivenY.HT + optY.HT >
      optYgivenX.HT + optX.HT + (c : ℝ) * Epiplexity.log2 (n : ℝ) := by
  have hn_pos : 0 < n :=
    lt_of_lt_of_le (by decide : 0 < 9) hn
  have hYgivenX : optYgivenX.HT ≤ 2 :=
    HT_Y_given_X_le_two (n := n) (T := T) (hn := hn_pos) e optYgivenX
  -- Uniform entropy bounds for `H_T(X)` and `H_T(Y)`.
  have hX_bounds : (n : ℝ) ≤ optX.HT ∧ optX.HT ≤ (n : ℝ) + (BitStr.uniformProg n).codeLen :=
    BitStr.lemma16_HT_bounds (n := n) (T := T) (opt := optX)
  have hY_bounds : (n : ℝ) ≤ optY.HT ∧ optY.HT ≤ (n : ℝ) + (BitStr.uniformProg n).codeLen :=
    BitStr.lemma16_HT_bounds (n := n) (T := T) (opt := optY)
  have hcode1 : (BitStr.uniformProg n).codeLen = 1 := BitStr.uniformProg_codeLen n
  have hY_minus_X : optY.HT - optX.HT ≥ -1 := by
    have hY_ge_n : (n : ℝ) ≤ optY.HT := hY_bounds.1
    have hX_le : optX.HT ≤ (n : ℝ) + 1 := by
      simpa [hcode1] using hX_bounds.2
    linarith
  -- Lower bound `H_T(X|Y) ≥ (c+1) log₂ n` from one-wayness.
  have hpos_cond : ∀ y, (optXgivenY.P.dist y).Pos := optXgivenY.P.distPos
  have hsuccess_le :
      invSuccess (n := n) e optXgivenY.P.dist ≤ 1 / ((n : ℝ) ^ (c + 1)) :=
    hOWP optXgivenY.P optXgivenY.feasible
  have hHXgivenY_ge :
      (c + 1 : ℝ) * Epiplexity.log2 (n : ℝ) ≤ optXgivenY.HT := by
    -- Jensen gives `HT ≥ log2(1/success)`, then use `success ≤ 1/n^(c+1)`.
    have hJ :
        Epiplexity.log2 (1 / invSuccess (n := n) e optXgivenY.P.dist) ≤ optXgivenY.HT := by
      simpa [OptimalCondProg.HT] using
        condCrossEntropyBits_jointYX_ge_log2_invSuccess (n := n) e optXgivenY.P.dist hpos_cond
    have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hpow_pos : 0 < (n : ℝ) ^ (c + 1) := by positivity
    have hsuccess_pos : 0 < invSuccess (n := n) e optXgivenY.P.dist :=
      invSuccess_pos (n := n) e optXgivenY.P.dist hpos_cond
    have hdiv_le :
        (n : ℝ) ^ (c + 1) ≤ 1 / invSuccess (n := n) e optXgivenY.P.dist := by
      have h :=
        one_div_le_one_div_of_le hsuccess_pos hsuccess_le
      simpa using h
    have hlog2_mono :
        Epiplexity.log2 ((n : ℝ) ^ (c + 1)) ≤ Epiplexity.log2 (1 / invSuccess (n := n) e optXgivenY.P.dist) := by
      -- `log2` is monotone on positive reals.
      have hlog_mono :
          Real.log ((n : ℝ) ^ (c + 1)) ≤ Real.log (1 / invSuccess (n := n) e optXgivenY.P.dist) :=
        Real.log_le_log (by positivity) hdiv_le
      have hlog2_pos : 0 < Real.log (2 : ℝ) := by
        have : (1 : ℝ) < 2 := by norm_num
        simpa using Real.log_pos this
      have := div_le_div_of_nonneg_right hlog_mono (le_of_lt hlog2_pos)
      simpa [Epiplexity.log2] using this
    have hlog2_pow :
        Epiplexity.log2 ((n : ℝ) ^ (c + 1)) = (c + 1 : ℝ) * Epiplexity.log2 (n : ℝ) := by
      -- `log2(n^(c+1)) = (c+1)*log2(n)` for `n>0`.
      unfold Epiplexity.log2
      simp [Real.log_pow, Nat.cast_add, Nat.cast_one, mul_div_assoc]
    have :
        (c + 1 : ℝ) * Epiplexity.log2 (n : ℝ) ≤ Epiplexity.log2 (1 / invSuccess (n := n) e optXgivenY.P.dist) := by
      simpa [hlog2_pow] using hlog2_mono
    exact le_trans this hJ
  -- Use the slack `log₂ n` to absorb the constant terms and get strict `>`.
  have hlog2_pos' : (3 : ℝ) < Epiplexity.log2 (n : ℝ) := by
    have hn_gt8 : (8 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 8 < 9) hn)
    have hlog2_pos : 0 < Real.log (2 : ℝ) := by
      have : (1 : ℝ) < 2 := by norm_num
      simpa using Real.log_pos this
    have hlog_mono : Real.log (8 : ℝ) < Real.log (n : ℝ) :=
      Real.log_lt_log (by norm_num) hn_gt8
    -- `log2 8 = 3`.
    have hlog2_8 : Epiplexity.log2 (8 : ℝ) = 3 := by
      unfold Epiplexity.log2
      have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      -- `8 = 2^3`.
      have : (8 : ℝ) = (2 : ℝ) ^ (3 : Nat) := by norm_num
      simp [this, Real.log_pow, hlog2_ne0]
    have hdiv : Epiplexity.log2 (8 : ℝ) < Epiplexity.log2 (n : ℝ) := by
      -- Divide `log` inequality by `log 2 > 0`.
      have := div_lt_div_of_pos_right hlog_mono hlog2_pos
      simpa [Epiplexity.log2] using this
    simpa [hlog2_8] using hdiv
  -- Assemble.
  have :
      optXgivenY.HT + optY.HT - (optYgivenX.HT + optX.HT + (c : ℝ) * Epiplexity.log2 (n : ℝ))
        >
      0 := by
    have : optXgivenY.HT + optY.HT
        ≥ (c : ℝ) * Epiplexity.log2 (n : ℝ) + (Epiplexity.log2 (n : ℝ)) + optX.HT - 1 := by
      -- `HT(X|Y) ≥ (c+1)log2 n` and `HT(Y) ≥ HT(X) - 1`.
      have h1 : (c + 1 : ℝ) * Epiplexity.log2 (n : ℝ) = (c : ℝ) * Epiplexity.log2 (n : ℝ) + Epiplexity.log2 (n : ℝ) := by
        ring
      have hY_ge : optY.HT ≥ optX.HT - 1 := by
        linarith [hY_minus_X]
      linarith [hHXgivenY_ge, hY_ge, h1]
    have : optYgivenX.HT + optX.HT + (c : ℝ) * Epiplexity.log2 (n : ℝ) ≤
        (c : ℝ) * Epiplexity.log2 (n : ℝ) + optX.HT + 2 := by
      linarith [hYgivenX]
    -- Now use `log2 n > 3` to beat the constants.
    linarith [hlog2_pos']
  linarith

/-!
Paper Theorem 25 / Theorem 13 are asymptotic. We package the asymptotic hypothesis as a
“negligible” success bound over the bit-length `n`.
-/

def OWPnegl (T : Nat) (e : (n : Nat) → BitStr n ≃ BitStr n) : Prop :=
  ∀ c : Nat, ∃ N : Nat, ∀ n ≥ N, OWPSecure (n := n) T (e n) (1 / ((n : ℝ) ^ c))

theorem theorem25 (T : Nat) (e : (n : Nat) → BitStr n ≃ BitStr n) (hOW : OWPnegl T e) :
    ∀ c : Nat, ∃ N : Nat, ∀ n ≥ N,
      ∀ optX : OptimalProg (α := BitStr n) T (Un n),
        ∀ optY : OptimalProg (α := BitStr n) T (Un n),
          ∀ optYgivenX :
              OptimalCondProg (α := BitStr n) (β := BitStr n) T (jointXY (n := n) (e n)),
            ∀ optXgivenY :
              OptimalCondProg (α := BitStr n) (β := BitStr n) T (jointYX (n := n) (e n)),
              optXgivenY.HT + optY.HT >
                optYgivenX.HT + optX.HT + (c : ℝ) * Epiplexity.log2 (n : ℝ) := by
  intro c
  -- Use negligible one-wayness with exponent `c+1`, then apply `theorem25_core` for `n ≥ 9`.
  rcases hOW (c + 1) with ⟨N0, hN0⟩
  refine ⟨Nat.max N0 9, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn9 : 9 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hsec :
      OWPSecure (n := n) T (e n) (1 / ((n : ℝ) ^ (c + 1))) := hN0 n hn0
  intro optX optY optYgivenX optXgivenY
  exact theorem25_core (n := n) (T := T) hn9 (e n) c hsec optX optY optYgivenX optXgivenY

theorem theorem13 (T : Nat) (e : (n : Nat) → BitStr n ≃ BitStr n) (hOW : OWPnegl T e) :
    ∀ c : Nat, ∃ N : Nat, ∀ n ≥ N,
      ∀ optX : OptimalProg (α := BitStr n) T (Un n),
        ∀ optY : OptimalProg (α := BitStr n) T (Un n),
          ∀ optYgivenX :
              OptimalCondProg (α := BitStr n) (β := BitStr n) T (jointXY (n := n) (e n)),
            ∀ optXgivenY :
              OptimalCondProg (α := BitStr n) (β := BitStr n) T (jointYX (n := n) (e n)),
              optXgivenY.HT + optY.HT >
                optYgivenX.HT + optX.HT + (c : ℝ) * Epiplexity.log2 (n : ℝ) :=
  theorem25 (T := T) (e := e) hOW

/-! ### Corollary 26: Bayes violation (pointwise) -/

theorem exists_pointwise_ratio_gt_of_expectation_gt
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : (∑ i : ι, w i) = 1)
    (r : ℝ) (hE : (∑ i : ι, w i * a i) > r) :
    ∃ i : ι, a i > r := by
  classical
  by_contra hno
  have ha_le : ∀ i : ι, a i ≤ r := by
    intro i
    have : ¬r < a i := by
      intro hlt
      exact hno ⟨i, hlt⟩
    exact le_of_not_gt this
  have hsum_le :
      (∑ i : ι, w i * a i) ≤ (∑ i : ι, w i * r) := by
    classical
    simpa using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _hi => by
        have := mul_le_mul_of_nonneg_left (ha_le i) (hw_nonneg i)
        simpa [mul_assoc] using this))
  have : (∑ i : ι, w i * r) = r := by
    classical
    calc
      (∑ i : ι, w i * r) = (∑ i : ι, w i) * r := by
        simpa using (Finset.sum_mul (s := (Finset.univ : Finset ι)) (f := w) (a := r)).symm
      _ = 1 * r := by simp [hw_sum]
      _ = r := by simp
  linarith [hsum_le, this]

theorem corollary26_core {n T : Nat} (hn : 9 ≤ n) (e : BitStr n ≃ BitStr n) (c : Nat)
    (hOWP : OWPSecure (n := n) T e (1 / ((n : ℝ) ^ (c + 1))))
    (P1 : Prog (BitStr n)) (P2 : CondProg (BitStr n) (BitStr n))
    (Q2 : Prog (BitStr n)) (Q1 : CondProg (BitStr n) (BitStr n))
    (_hP1 : Prog.Feasible T P1) (_hP2 : CondProg.Feasible T P2)
    (_hQ2 : Prog.Feasible T Q2) (hQ1 : CondProg.Feasible T Q1)
    (ε : ℝ)
    (hFitX : Info.crossEntropyBits (Un n) P1.dist ≤ (n : ℝ) + ε)
    (hFitYgivenX :
      condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointXY (n := n) e) P2.dist ≤ ε) :
    ∃ x : BitStr n,
      (P1.dist.pmf x) * (P2.dist x).pmf (e x)
        >
      ((n : ℝ) ^ (c : ℕ)) * ((2 : ℝ) ^ (-(2 * ε))) * (Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x := by
  classical
  have hn_pos : 0 < n :=
    lt_of_lt_of_le (by decide : 0 < 9) hn
  -- Lower bounds on reverse-direction terms.
  have hUn_pos : (Un n).Pos := Epiplexity.FinDist.uniform_Pos (α := BitStr n)
  have hce_Q2 : (n : ℝ) ≤ Info.crossEntropyBits (Un n) Q2.dist := by
    have hEnt : Info.entropyBits (Un n) = n := BitStr.entropyBits_uniform (n := n)
    have hge :
        Info.entropyBits (Un n) ≤ Info.crossEntropyBits (Un n) Q2.dist :=
      Info.crossEntropyBits_ge_entropyBits (p := Un n) (q := Q2.dist) hUn_pos Q2.distPos
    simpa [hEnt] using hge
  have hpos_cond : ∀ y, (Q1.dist y).Pos := Q1.distPos
  have hsuccess_le :
      invSuccess (n := n) e Q1.dist ≤ 1 / ((n : ℝ) ^ (c + 1)) :=
    hOWP Q1 hQ1
  have hHXgivenY_ge :
      (c + 1 : ℝ) * Epiplexity.log2 (n : ℝ)
        ≤ condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q1.dist := by
    have hJ :
        Epiplexity.log2 (1 / invSuccess (n := n) e Q1.dist) ≤
          condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q1.dist := by
      exact condCrossEntropyBits_jointYX_ge_log2_invSuccess (n := n) e Q1.dist hpos_cond
    have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hpow_pos : 0 < (n : ℝ) ^ (c + 1) := by positivity
    have hsuccess_pos : 0 < invSuccess (n := n) e Q1.dist := invSuccess_pos (n := n) e Q1.dist hpos_cond
    have hdiv_le :
        (n : ℝ) ^ (c + 1) ≤ 1 / invSuccess (n := n) e Q1.dist := by
      have h := one_div_le_one_div_of_le hsuccess_pos hsuccess_le
      simpa using h
    have hlog2_mono :
        Epiplexity.log2 ((n : ℝ) ^ (c + 1)) ≤ Epiplexity.log2 (1 / invSuccess (n := n) e Q1.dist) := by
      have hlog_mono :
          Real.log ((n : ℝ) ^ (c + 1)) ≤ Real.log (1 / invSuccess (n := n) e Q1.dist) :=
        Real.log_le_log (by positivity) hdiv_le
      have hlog2_pos : 0 < Real.log (2 : ℝ) := by
        have : (1 : ℝ) < 2 := by norm_num
        simpa using Real.log_pos this
      have := div_le_div_of_nonneg_right hlog_mono (le_of_lt hlog2_pos)
      simpa [Epiplexity.log2] using this
    have hlog2_pow :
        Epiplexity.log2 ((n : ℝ) ^ (c + 1)) = (c + 1 : ℝ) * Epiplexity.log2 (n : ℝ) := by
      unfold Epiplexity.log2
      simp [Real.log_pow, Nat.cast_add, Nat.cast_one, mul_div_assoc]
    have :
        (c + 1 : ℝ) * Epiplexity.log2 (n : ℝ) ≤ Epiplexity.log2 (1 / invSuccess (n := n) e Q1.dist) := by
      simpa [hlog2_pow] using hlog2_mono
    exact le_trans this hJ
  -- Expected log2 ratio lower bound.
  let w : BitStr n → ℝ := fun x => (Un n).pmf x
  let a : BitStr n → ℝ :=
    fun x =>
      Epiplexity.log2 ((P1.dist.pmf x) * (P2.dist x).pmf (e x)
        / ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x))
  have hw_nonneg : ∀ x, 0 ≤ w x := fun x => (Un n).nonneg x
  have hw_sum : (∑ x : BitStr n, w x) = 1 := by
    simp [w, Un]
  have hE :
      (∑ x : BitStr n, w x * a x)
        > (c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε := by
    -- Expand `a` into logs and use the fit/lower-bound hypotheses.
    -- We use the inequality with a *strict* gap coming from the `(c+1)` term.
    have hpos_den :
        ∀ x : BitStr n, 0 < (Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x := by
      intro x
      exact mul_pos (Q2.distPos _) (Q1.distPos _ _)
    have hpos_num :
        ∀ x : BitStr n, 0 < (P1.dist.pmf x) * (P2.dist x).pmf (e x) := by
      intro x
      exact mul_pos (P1.distPos _) (P2.distPos _ _)
    -- Lower bound `E[log2 ratio]` using `log2` linearity and the cross-entropy bounds.
    have hlog2_pos : 0 < Real.log (2 : ℝ) := by
      have : (1 : ℝ) < 2 := by norm_num
      simpa using Real.log_pos this
    have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
    -- Convert expectations of `log2 pmf` into `-` cross-entropy bits.
    have hE_P1 :
        (∑ x : BitStr n, w x * Epiplexity.log2 (P1.dist.pmf x))
          = -Info.crossEntropyBits (Un n) P1.dist := by
      classical
      unfold Epiplexity.log2 Info.crossEntropyBits Info.nllBits Info.nllNat
      -- With `P1.distPos`, `safeLog = log`.
      have hsafelog : ∀ x : BitStr n,
          InfoTheory.safeLog (P1.dist.pmf x) = Real.log (P1.dist.pmf x) :=
        fun x => InfoTheory.safeLog_of_pos (P1.distPos x)
      simp [w, hsafelog, div_eq_mul_inv, mul_assoc, mul_comm]
    have hE_Q2 :
        (∑ x : BitStr n, w x * Epiplexity.log2 (Q2.dist.pmf (e x)))
          = -Info.crossEntropyBits (Un n) Q2.dist := by
      classical
      -- Change of variables `y := e x` (uniform weights are invariant).
      have hperm :
          (∑ x : BitStr n, w x * Epiplexity.log2 (Q2.dist.pmf (e x)))
            = ∑ y : BitStr n, w y * Epiplexity.log2 (Q2.dist.pmf y) := by
        refine Fintype.sum_equiv e
          (fun x : BitStr n => w x * Epiplexity.log2 (Q2.dist.pmf (e x)))
          (fun y : BitStr n => w y * Epiplexity.log2 (Q2.dist.pmf y)) ?_
        intro x
        simp [w, Un, Epiplexity.FinDist.uniform_pmf]
      rw [hperm]
      -- Now identical to `hE_P1`, but with `Q2`.
      unfold Epiplexity.log2 Info.crossEntropyBits Info.nllBits Info.nllNat
      have hsafelog : ∀ x : BitStr n,
          InfoTheory.safeLog (Q2.dist.pmf x) = Real.log (Q2.dist.pmf x) :=
        fun x => InfoTheory.safeLog_of_pos (Q2.distPos x)
      simp [w, hsafelog, div_eq_mul_inv, mul_assoc, mul_comm]
    -- For the conditional terms, we use the joint distributions.
    have hE_P2 :
        (∑ x : BitStr n, w x * Epiplexity.log2 ((P2.dist x).pmf (e x)))
          = -condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointXY (n := n) e) P2.dist := by
      classical
      -- Expand the joint sum and simplify using the graph form (only `y = e x` contributes).
      have hjoint :
          condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointXY (n := n) e) P2.dist
            = ∑ x : BitStr n, w x * Info.nllBits (P2.dist x) (e x) := by
        unfold condCrossEntropyBits condNllBits
        -- Similar to `condCrossEntropyBits_jointYX_eq`.
        have hswap :
            (∑ xy : BitStr n × BitStr n,
                (jointXY (n := n) e).pmf xy * Info.nllBits (P2.dist xy.1) xy.2)
              =
            ∑ x : BitStr n, ∑ y : BitStr n,
                (jointXY (n := n) e).pmf (x, y) * Info.nllBits (P2.dist x) y := by
          simpa using (Fintype.sum_prod_type
            (fun xy : BitStr n × BitStr n =>
              (jointXY (n := n) e).pmf xy * Info.nllBits (P2.dist xy.1) xy.2))
        rw [hswap]
        have hinner :
            ∀ x : BitStr n,
              (∑ y : BitStr n,
                  (jointXY (n := n) e).pmf (x, y) * Info.nllBits (P2.dist x) y)
                = w x * Info.nllBits (P2.dist x) (e x) := by
          intro x
          have hpmf : ∀ y : BitStr n,
              (jointXY (n := n) e).pmf (x, y) = if y = e x then w x else 0 := by
            intro y
            by_cases hy : y = e x
            · subst hy
              simp [jointXY, w, Un, Epiplexity.FinDist.uniform_pmf]
            · simp [jointXY, w, hy]
          -- Rewrite the pmf as an `if` and let `simp` compute the single nonzero term.
          classical
          simp [hpmf]
        apply Fintype.sum_congr
        intro x
        simpa using hinner x
      -- Now translate `nllBits` to `log2`.
      have hsafelog : ∀ x : BitStr n,
          InfoTheory.safeLog ((P2.dist x).pmf (e x)) = Real.log ((P2.dist x).pmf (e x)) :=
        fun x => InfoTheory.safeLog_of_pos (P2.distPos x _)
      -- Finish.
      rw [hjoint]
      unfold Epiplexity.log2
      simp [Info.nllBits, Info.nllNat, hsafelog, w, div_eq_mul_inv]
      -- `simp` closes the algebraic goal.
    -- For the hard reverse conditional term, use `condCrossEntropyBits_jointYX_eq`.
    have hE_Q1 :
        (∑ x : BitStr n, w x * Epiplexity.log2 ((Q1.dist (e x)).pmf x))
          = -condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q1.dist := by
      classical
      -- Change variables to sum over `y := e x`.
      have hperm :
          (∑ x : BitStr n, w x * Epiplexity.log2 ((Q1.dist (e x)).pmf x))
            =
          ∑ y : BitStr n, w y * Epiplexity.log2 ((Q1.dist y).pmf (e.symm y)) := by
        -- Use `Fintype.sum_equiv` with `e.symm`.
        have :
            (∑ y : BitStr n, w (e.symm y) * Epiplexity.log2 ((Q1.dist y).pmf (e.symm y)))
              =
            ∑ y : BitStr n, w y * Epiplexity.log2 ((Q1.dist y).pmf (e.symm y)) := by
          -- `w` is uniform, so `w (e.symm y) = w y`.
          have hwconst : ∀ y : BitStr n, w (e.symm y) = w y := by
            intro y
            simp [w, Un, Epiplexity.FinDist.uniform_pmf]
          simp [hwconst]
        -- Now rewrite the LHS as the original sum.
        -- `Fintype.sum_equiv` with `e`:
        have h1 :
            (∑ x : BitStr n, w x * Epiplexity.log2 ((Q1.dist (e x)).pmf x))
              =
            ∑ y : BitStr n, w (e.symm y) * Epiplexity.log2 ((Q1.dist y).pmf (e.symm y)) := by
          refine Fintype.sum_equiv e
            (fun x : BitStr n => w x * Epiplexity.log2 ((Q1.dist (e x)).pmf x))
            (fun y : BitStr n => w (e.symm y) * Epiplexity.log2 ((Q1.dist y).pmf (e.symm y))) ?_
          intro x
          simp
        simpa [h1] using this
      -- Rewrite the goal in terms of the `y`-sum.
      rw [hperm]
      -- Translate the RHS sum to `-` conditional cross-entropy using `condCrossEntropyBits_jointYX_eq`.
      have hjoint :
          condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q1.dist
            = ∑ y : BitStr n, w y * Info.nllBits (Q1.dist y) (e.symm y) := by
        simpa [w] using condCrossEntropyBits_jointYX_eq (n := n) e Q1.dist
      have hsafelog : ∀ y : BitStr n,
          InfoTheory.safeLog ((Q1.dist y).pmf (e.symm y)) = Real.log ((Q1.dist y).pmf (e.symm y)) :=
        fun y => InfoTheory.safeLog_of_pos (Q1.distPos y _)
      unfold Epiplexity.log2
      unfold Info.nllBits Info.nllNat at hjoint
      -- Finish.
      simp [hjoint, hsafelog, w, div_eq_mul_inv]
    -- Combine the four pieces into the expected log-ratio.
    have hmain :
        (∑ x : BitStr n, w x * a x)
          =
        -(Info.crossEntropyBits (Un n) P1.dist)
        - (condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointXY (n := n) e) P2.dist)
        + (Info.crossEntropyBits (Un n) Q2.dist)
        + (condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q1.dist) := by
      classical
      have ha :
          ∀ x : BitStr n,
            a x =
              (Epiplexity.log2 (P1.dist.pmf x) + Epiplexity.log2 ((P2.dist x).pmf (e x)))
                -
              (Epiplexity.log2 (Q2.dist.pmf (e x)) + Epiplexity.log2 ((Q1.dist (e x)).pmf x)) := by
        intro x
        have hp1_ne0 : P1.dist.pmf x ≠ 0 := ne_of_gt (P1.distPos x)
        have hp2_ne0 : (P2.dist x).pmf (e x) ≠ 0 := ne_of_gt (P2.distPos x (e x))
        have hq2_ne0 : Q2.dist.pmf (e x) ≠ 0 := ne_of_gt (Q2.distPos (e x))
        have hq1_ne0 : (Q1.dist (e x)).pmf x ≠ 0 := ne_of_gt (Q1.distPos (e x) x)
        have hlog :
            Real.log ((P1.dist.pmf x) * (P2.dist x).pmf (e x) /
                ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x))
              =
            (Real.log (P1.dist.pmf x) + Real.log ((P2.dist x).pmf (e x)))
              - (Real.log (Q2.dist.pmf (e x)) + Real.log ((Q1.dist (e x)).pmf x)) := by
          calc
            Real.log ((P1.dist.pmf x) * (P2.dist x).pmf (e x) /
                ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x))
                =
              Real.log ((P1.dist.pmf x) * (P2.dist x).pmf (e x))
                  - Real.log ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x) := by
                simpa using
                  Real.log_div (mul_ne_zero hp1_ne0 hp2_ne0) (mul_ne_zero hq2_ne0 hq1_ne0)
            _ =
              (Real.log (P1.dist.pmf x) + Real.log ((P2.dist x).pmf (e x)))
                  - (Real.log (Q2.dist.pmf (e x)) + Real.log ((Q1.dist (e x)).pmf x)) := by
                simp [Real.log_mul hp1_ne0 hp2_ne0, Real.log_mul hq2_ne0 hq1_ne0]
        dsimp [a]
        unfold Epiplexity.log2
        rw [hlog]
        ring
      have hdecomp :
          (∑ x : BitStr n, w x * a x)
            =
          (∑ x : BitStr n, w x * Epiplexity.log2 (P1.dist.pmf x))
            + (∑ x : BitStr n, w x * Epiplexity.log2 ((P2.dist x).pmf (e x)))
            - ((∑ x : BitStr n, w x * Epiplexity.log2 (Q2.dist.pmf (e x)))
                + (∑ x : BitStr n, w x * Epiplexity.log2 ((Q1.dist (e x)).pmf x))) := by
        calc
          (∑ x : BitStr n, w x * a x)
              =
              ∑ x : BitStr n,
                w x *
                  ((Epiplexity.log2 (P1.dist.pmf x) + Epiplexity.log2 ((P2.dist x).pmf (e x)))
                    -
                      (Epiplexity.log2 (Q2.dist.pmf (e x)) + Epiplexity.log2 ((Q1.dist (e x)).pmf x))) := by
                refine Fintype.sum_congr
                  (fun x : BitStr n => w x * a x)
                  (fun x : BitStr n =>
                    w x *
                      ((Epiplexity.log2 (P1.dist.pmf x) + Epiplexity.log2 ((P2.dist x).pmf (e x)))
                        - (Epiplexity.log2 (Q2.dist.pmf (e x)) + Epiplexity.log2 ((Q1.dist (e x)).pmf x))))
                  (fun x => by simp [ha x])
          _ =
              ∑ x : BitStr n,
                (w x *
                    (Epiplexity.log2 (P1.dist.pmf x) + Epiplexity.log2 ((P2.dist x).pmf (e x)))
                  -
                  w x *
                    (Epiplexity.log2 (Q2.dist.pmf (e x)) + Epiplexity.log2 ((Q1.dist (e x)).pmf x))) := by
                simp [mul_sub]
          _ =
              (∑ x : BitStr n,
                  w x * (Epiplexity.log2 (P1.dist.pmf x) + Epiplexity.log2 ((P2.dist x).pmf (e x))))
                -
                (∑ x : BitStr n,
                  w x * (Epiplexity.log2 (Q2.dist.pmf (e x)) + Epiplexity.log2 ((Q1.dist (e x)).pmf x))) := by
                simp [Finset.sum_sub_distrib]
          _ =
              (∑ x : BitStr n, w x * Epiplexity.log2 (P1.dist.pmf x))
                + (∑ x : BitStr n, w x * Epiplexity.log2 ((P2.dist x).pmf (e x)))
                -
                  ((∑ x : BitStr n, w x * Epiplexity.log2 (Q2.dist.pmf (e x)))
                    + (∑ x : BitStr n, w x * Epiplexity.log2 ((Q1.dist (e x)).pmf x))) := by
                have hleft :
                    (∑ x : BitStr n,
                        w x *
                          (Epiplexity.log2 (P1.dist.pmf x) +
                            Epiplexity.log2 ((P2.dist x).pmf (e x))))
                      =
                    (∑ x : BitStr n, w x * Epiplexity.log2 (P1.dist.pmf x))
                      + (∑ x : BitStr n, w x * Epiplexity.log2 ((P2.dist x).pmf (e x))) := by
                  simp [Finset.sum_add_distrib, mul_add]
                have hright :
                    (∑ x : BitStr n,
                        w x *
                          (Epiplexity.log2 (Q2.dist.pmf (e x)) +
                            Epiplexity.log2 ((Q1.dist (e x)).pmf x)))
                      =
                    (∑ x : BitStr n, w x * Epiplexity.log2 (Q2.dist.pmf (e x)))
                      + (∑ x : BitStr n, w x * Epiplexity.log2 ((Q1.dist (e x)).pmf x)) := by
                  simp [Finset.sum_add_distrib, mul_add]
                rw [hleft, hright]
      rw [hdecomp, hE_P1, hE_P2, hE_Q2, hE_Q1]
      ring
    -- Apply bounds.
    have hstrict :
        -(Info.crossEntropyBits (Un n) P1.dist)
        - (condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointXY (n := n) e) P2.dist)
        + (Info.crossEntropyBits (Un n) Q2.dist)
        + (condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q1.dist)
          >
        (c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε := by
      -- Use `crossEntropy(Q2) ≥ n` and `condCrossEntropy(Q1) ≥ (c+1)log2 n`.
      have hHX : (c : ℝ) * Epiplexity.log2 (n : ℝ) + Epiplexity.log2 (n : ℝ)
          ≤ condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointYX (n := n) e) Q1.dist := by
        have : (c + 1 : ℝ) * Epiplexity.log2 (n : ℝ)
            = (c : ℝ) * Epiplexity.log2 (n : ℝ) + Epiplexity.log2 (n : ℝ) := by ring
        linarith [hHXgivenY_ge, this]
      have hlog2_pos' : (0 : ℝ) < Epiplexity.log2 (n : ℝ) := by
        have hn_gt1 : (1 : ℝ) < (n : ℝ) := by
          have : 1 < n := Nat.lt_of_lt_of_le (by decide : 1 < 9) hn
          exact_mod_cast this
        have hlog2_pos : 0 < Real.log (2 : ℝ) := by
          have : (1 : ℝ) < 2 := by norm_num
          simpa using Real.log_pos this
        have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt1
        have := div_pos hlog hlog2_pos
        simpa [Epiplexity.log2] using this
      -- Combine all bounds.
      linarith [hFitX, hFitYgivenX, hce_Q2, hHX, hlog2_pos']
    -- Done.
    simpa [hmain] using hstrict
  -- Extract a pointwise witness from the expectation bound.
  have hex :
      ∃ x : BitStr n,
        a x > (c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε :=
    exists_pointwise_ratio_gt_of_expectation_gt (ι := BitStr n) w a hw_nonneg hw_sum
      ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε) hE
  rcases hex with ⟨x, hx⟩
  -- Exponentiate `log2` to get the multiplicative Bayes-ratio bound.
  have hpos_ratio :
      0 < (P1.dist.pmf x) * (P2.dist x).pmf (e x) /
        ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x) := by
    have hnum : 0 < (P1.dist.pmf x) * (P2.dist x).pmf (e x) := mul_pos (P1.distPos _) (P2.distPos _ _)
    have hden : 0 < (Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x := mul_pos (Q2.distPos _) (Q1.distPos _ _)
    exact div_pos hnum hden
  have hx' :
      (P1.dist.pmf x) * (P2.dist x).pmf (e x) /
          ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x)
        >
      (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε) := by
    -- `log2 r > t` implies `r > 2^t`.
    have hx0 :
        Real.log ((P1.dist.pmf x) * (P2.dist x).pmf (e x) /
            ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x)) / Real.log 2
          >
        (c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε := by
      simpa [a, Epiplexity.log2] using hx
    have hlog2_pos : 0 < Real.log (2 : ℝ) := by
      have : (1 : ℝ) < 2 := by norm_num
      simpa using Real.log_pos this
    have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
    have hxlog :
        Real.log ((P1.dist.pmf x) * (P2.dist x).pmf (e x) /
            ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x))
          >
        ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε) * Real.log 2 := by
      have := (mul_lt_mul_of_pos_right hx0 hlog2_pos)
      simpa [div_eq_mul_inv, hlog2_ne0, mul_assoc] using this
    have hxlog' : Real.log 2 * ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε) <
        Real.log ((P1.dist.pmf x) * (P2.dist x).pmf (e x) /
          ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x)) := by
      have : ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε) * Real.log 2 <
          Real.log ((P1.dist.pmf x) * (P2.dist x).pmf (e x) /
            ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x)) := by
        simpa [gt_iff_lt] using hxlog
      simpa [mul_comm] using this
    have hexp :
        Real.exp (Real.log 2 * ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε))
          <
        (P1.dist.pmf x) * (P2.dist x).pmf (e x) /
          ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x) :=
      (Real.lt_log_iff_exp_lt hpos_ratio).1 hxlog'
    have h2pos : (0 : ℝ) < 2 := by norm_num
    -- Rewrite `exp(log 2 * t)` as `2^t`.
    have : (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε) <
        (P1.dist.pmf x) * (P2.dist x).pmf (e x) /
          ((Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x) := by
      simpa [Real.rpow_def_of_pos h2pos] using hexp
    exact this
  -- Rewrite the RHS into the requested `n^c * 2^{-2ε}` form.
  have hrhs :
      (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε)
        = ((n : ℝ) ^ (c : ℕ)) * ((2 : ℝ) ^ (-(2 * ε))) := by
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have h2nonneg : (0 : ℝ) ≤ 2 := le_of_lt h2pos
    have hlog2_pos : 0 < Real.log (2 : ℝ) := by
      have : (1 : ℝ) < 2 := by norm_num
      simpa using Real.log_pos this
    have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
    have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hmul : Real.log (2 : ℝ) * (Real.log (n : ℝ) / Real.log 2) = Real.log (n : ℝ) := by
      simp [div_eq_mul_inv]
      calc
        Real.log 2 * (Real.log (n : ℝ) * (Real.log 2)⁻¹)
            = Real.log (n : ℝ) * (Real.log 2 * (Real.log 2)⁻¹) := by ring_nf
        _ = Real.log (n : ℝ) := by simp [hlog2_ne0]
    have hbase : (2 : ℝ) ^ Epiplexity.log2 (n : ℝ) = (n : ℝ) := by
      unfold Epiplexity.log2
      calc
        (2 : ℝ) ^ (Real.log (n : ℝ) / Real.log 2)
            = Real.exp (Real.log 2 * (Real.log (n : ℝ) / Real.log 2)) := by
                simp [Real.rpow_def_of_pos h2pos]
        _ = Real.exp (Real.log (n : ℝ)) := by simp [hmul]
        _ = (n : ℝ) := by exact Real.exp_log hnR_pos
    have hpow : (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ)) = (n : ℝ) ^ (c : ℕ) := by
      have hc : (c : ℝ) * Epiplexity.log2 (n : ℝ) = Epiplexity.log2 (n : ℝ) * (c : ℝ) := by ring
      calc
        (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ))
            = (2 : ℝ) ^ (Epiplexity.log2 (n : ℝ) * (c : ℝ)) := by simp [hc]
        _ = ((2 : ℝ) ^ Epiplexity.log2 (n : ℝ)) ^ (c : ℝ) := by
              exact Real.rpow_mul (x := (2 : ℝ)) h2nonneg (Epiplexity.log2 (n : ℝ)) (c : ℝ)
        _ = ((2 : ℝ) ^ Epiplexity.log2 (n : ℝ)) ^ c := by
              exact Real.rpow_natCast ((2 : ℝ) ^ Epiplexity.log2 (n : ℝ)) c
        _ = (n : ℝ) ^ (c : ℕ) := by simp [hbase]
    calc
      (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε)
          = (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ)) * (2 : ℝ) ^ (-(2 * ε)) := by
              simpa [sub_eq_add_neg] using
                (Real.rpow_add h2pos ((c : ℝ) * Epiplexity.log2 (n : ℝ)) (-(2 * ε)))
      _ = ((n : ℝ) ^ (c : ℕ)) * ((2 : ℝ) ^ (-(2 * ε))) := by simp [hpow]
  refine ⟨x, ?_⟩
  have hden_pos : 0 < (Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x :=
    mul_pos (Q2.distPos _) (Q1.distPos _ _)
  -- Avoid expanding `(a*b)⁻¹` by treating the denominator as a single term.
  let d : ℝ := (Q2.dist.pmf (e x)) * (Q1.dist (e x)).pmf x
  have hd_pos : 0 < d := by simpa [d] using hden_pos
  have hd_ne0 : d ≠ 0 := ne_of_gt hd_pos
  have hx'' :
      (P1.dist.pmf x) * (P2.dist x).pmf (e x) / d
        >
      (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε) := by
    simpa [d] using hx'
  have hmul := mul_lt_mul_of_pos_right hx'' hd_pos
  have hclear :
      (2 : ℝ) ^ ((c : ℝ) * Epiplexity.log2 (n : ℝ) - 2 * ε) * d
        <
      (P1.dist.pmf x) * (P2.dist x).pmf (e x) := by
    simpa [div_eq_mul_inv, hd_ne0, mul_assoc] using hmul
  have hclear' :
      ((n : ℝ) ^ (c : ℕ)) * ((2 : ℝ) ^ (-(2 * ε))) * d
        <
      (P1.dist.pmf x) * (P2.dist x).pmf (e x) := by
    simpa [hrhs, mul_assoc] using hclear
  -- Unfold `d` and flip to `>` in the goal.
  simpa [d, mul_assoc] using hclear'

theorem corollary26 (T : Nat) (e : (n : Nat) → BitStr n ≃ BitStr n) (hOW : OWPnegl T e) :
    ∀ c : Nat, ∃ N : Nat, ∀ n ≥ N,
      ∀ P1 : Prog (BitStr n), ∀ P2 : CondProg (BitStr n) (BitStr n),
        ∀ Q2 : Prog (BitStr n), ∀ Q1 : CondProg (BitStr n) (BitStr n),
          ∀ _hP1 : Prog.Feasible T P1, ∀ _hP2 : CondProg.Feasible T P2,
            ∀ _hQ2 : Prog.Feasible T Q2, ∀ _hQ1 : CondProg.Feasible T Q1,
              ∀ ε : ℝ,
                Info.crossEntropyBits (Un n) P1.dist ≤ (n : ℝ) + ε →
                condCrossEntropyBits (α := BitStr n) (β := BitStr n) (jointXY (n := n) (e n)) P2.dist ≤ ε →
                ∃ x : BitStr n,
                  (P1.dist.pmf x) * (P2.dist x).pmf ((e n) x)
                    >
                  ((n : ℝ) ^ (c : ℕ)) * ((2 : ℝ) ^ (-(2 * ε))) *
                    (Q2.dist.pmf ((e n) x)) * (Q1.dist ((e n) x)).pmf x := by
  intro c
  rcases hOW (c + 1) with ⟨N0, hN0⟩
  refine ⟨Nat.max N0 9, ?_⟩
  intro n hn P1 P2 Q2 Q1 hP1 hP2 hQ2 _hQ1 ε hFitX hFitYgivenX
  have hn0 : N0 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn9 : 9 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hsec : OWPSecure (n := n) T (e n) (1 / ((n : ℝ) ^ (c + 1))) := hN0 n hn0
  exact corollary26_core (n := n) (T := T) hn9 (e n) c hsec P1 P2 Q2 Q1 hP1 hP2 hQ2 _hQ1 ε hFitX hFitYgivenX

end Factorization

end

end Crypto
end Epiplexity
end HeytingLean
