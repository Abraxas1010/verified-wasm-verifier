import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Algebra.Ring.Parity

/-!
# MirandaDynamics.Billiards: Cantor tape encoding + head-position embedding

This file mechanizes the core analytic/algebraic content of Miranda & Ramos
“Classical billiards can compute” (arXiv:2512.19156, Dec 2025), §3.1:

* encode a bi-infinite binary tape into the ternary Cantor set,
* embed head positions `k : ℤ` into pairwise-disjoint subintervals via affine maps `τ_k`,
* prove the “shift law” for `τ_{k+1}` in terms of `τ_k`.

All results avoid proof holes and rely on mathlib’s existing Cantor-function lemmas for the
summability/injectivity spine.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set
open Cardinal

/-! ## Tape states and the Cantor encoding -/

/-- A bi-infinite binary tape (paper alphabet `{0,1}`), indexed by `ℤ`. -/
abbrev Tape : Type :=
  ℤ → Bool

/-- The paper’s interleaving of `ℤ`-indices into `ℕ`:

* even `n` picks the nonnegative cell `n/2`,
* odd  `n` picks the negative cell `-(n/2+1)` (written as `Int.negSucc (n/2)`).

So `0, -1, 1, -2, 2, ...` appears in order. -/
def tapeIndex (n : ℕ) : ℤ :=
  if Even n then Int.ofNat (n / 2) else Int.negSucc (n / 2)

/-- The inverse map `ℤ → ℕ` matching `tapeIndex`:
`0 ↦ 0`, `1 ↦ 2`, `-1 ↦ 1`, `2 ↦ 4`, `-2 ↦ 3`, ... -/
def indexNat : ℤ → ℕ
  | Int.ofNat n => 2 * n
  | Int.negSucc n => 2 * n + 1

theorem tapeIndex_indexNat (z : ℤ) : tapeIndex (indexNat z) = z := by
  cases z with
  | ofNat n =>
    have hEven : Even (2 * n) := even_two_mul n
    have hDiv : (2 * n) / 2 = n :=
      Nat.mul_div_right n (m := 2) (Nat.succ_pos 1)
    simp [tapeIndex, indexNat, hEven, hDiv]
  | negSucc n =>
    have hOdd : ¬Even (2 * n + 1) := Nat.not_even_bit1 n
    have hDiv : (2 * n + 1) / 2 = n := by
      -- `2*n+1 = 1 + n*2` and `(1 + n*2)/2 = 1/2 + n = n`.
      have h := Nat.add_mul_div_right 1 n (Nat.succ_pos 1)
      calc
        (2 * n + 1) / 2 = (1 + n * 2) / 2 := by simp [Nat.mul_comm, Nat.add_comm]
        _ = 1 / 2 + n := h
        _ = n := by simp
    simp [tapeIndex, indexNat, hOdd, hDiv]

/-- The digit stream used in the ternary expansion: `digits t n = t (tapeIndex n)`. -/
def digits (t : Tape) : ℕ → Bool :=
  fun n => t (tapeIndex n)

theorem digits_injective : Function.Injective digits := by
  intro t₁ t₂ h
  funext z
  have := congrArg (fun f => f (indexNat z)) h
  simpa [digits, tapeIndex_indexNat] using this

/-! ### Cantor-set encoding for `{0,1}^ℕ` (scaled to ternary digits `{0,2}`) -/

/-- The Cantor-set value associated to a boolean digit stream:

`cantorEncode f = 2 * Σ f_n * 3^{-(n+1)}`  (implemented via `Cardinal.cantorFunction`).

This matches the paper’s `ε_i ∈ {0,2}` ternary expansion with `ε_{n+1} = if f n then 2 else 0`. -/
noncomputable def cantorEncode (f : ℕ → Bool) : ℝ :=
  (2 / 3 : ℝ) * Cardinal.cantorFunction (1 / 3) f

theorem cantorEncode_injective : Function.Injective cantorEncode := by
  intro f g hfg
  have hcf : Cardinal.cantorFunction (1 / 3) f = Cardinal.cantorFunction (1 / 3) g := by
    have hne : (2 / 3 : ℝ) ≠ 0 := by norm_num
    exact (mul_left_cancel₀ hne) (by simpa [cantorEncode] using hfg)
  have hinj : Function.Injective (Cardinal.cantorFunction (1 / 3)) :=
    Cardinal.cantorFunction_injective (by norm_num) (by norm_num)
  exact hinj hcf

/-- The paper’s tape encoding `t ↦ x_t ∈ [0,1]`. -/
noncomputable def encodeTape (t : Tape) : ℝ :=
  cantorEncode (digits t)

theorem encodeTape_injective : Function.Injective encodeTape := by
  intro t₁ t₂ h
  apply digits_injective
  apply cantorEncode_injective
  simpa [encodeTape] using h

/-! ### Basic bounds and Cantor-set membership -/

theorem cantorEncode_le_one (f : ℕ → Bool) : cantorEncode f ≤ 1 := by
  -- Compare against the all-`true` digit stream.
  have h0 : 0 ≤ (1 / 3 : ℝ) := by norm_num
  have h1 : (1 / 3 : ℝ) < 1 := by norm_num
  have hle :
      Cardinal.cantorFunction (1 / 3) f ≤ Cardinal.cantorFunction (1 / 3) (fun _ => true) :=
    Cardinal.cantorFunction_le h0 h1 (by intro _ _; simp)
  have hgeom : Cardinal.cantorFunction (1 / 3 : ℝ) (fun _ : ℕ => true) = (1 - (1 / 3 : ℝ))⁻¹ := by
    have h0' : 0 ≤ ((3 : ℝ)⁻¹) := by positivity
    have h1' : ((3 : ℝ)⁻¹) < 1 := by norm_num
    have hseries : (∑' n : ℕ, ((3 : ℝ) ^ n)⁻¹) = (1 - ((3 : ℝ)⁻¹))⁻¹ := by
      have hrew : (fun n : ℕ => ((3 : ℝ) ^ n)⁻¹) = fun n : ℕ => ((3 : ℝ)⁻¹) ^ n := by
        funext n
        have hpow : ((3 : ℝ)⁻¹) ^ n = ((3 : ℝ) ^ n)⁻¹ := inv_pow (3 : ℝ) n
        exact hpow.symm
      have hgeom' : (∑' n : ℕ, ((3 : ℝ)⁻¹) ^ n) = (1 - ((3 : ℝ)⁻¹))⁻¹ :=
        tsum_geometric_of_lt_one h0' h1'
      simpa [hrew] using hgeom'
    calc
      Cardinal.cantorFunction (1 / 3 : ℝ) (fun _ : ℕ => true) = (∑' n : ℕ, ((3 : ℝ) ^ n)⁻¹) := by
        simp [Cardinal.cantorFunction, Cardinal.cantorFunctionAux]
      _ = (1 - (1 / 3 : ℝ))⁻¹ := by
        simpa [one_div] using hseries
  have hcf : Cardinal.cantorFunction (1 / 3) f ≤ (1 - (1 / 3 : ℝ))⁻¹ := by
    exact hle.trans_eq hgeom
  have hpos : 0 ≤ (2 / 3 : ℝ) := by norm_num
  have hmul : cantorEncode f ≤ (2 / 3 : ℝ) * (1 - (1 / 3 : ℝ))⁻¹ := by
    simpa [cantorEncode] using mul_le_mul_of_nonneg_left hcf hpos
  have hrhs : (2 / 3 : ℝ) * (1 - (1 / 3 : ℝ))⁻¹ = (1 : ℝ) := by norm_num
  exact hmul.trans_eq hrhs

theorem cantorEncode_nonneg (f : ℕ → Bool) : 0 ≤ cantorEncode f := by
  have h0 : 0 ≤ (1 / 3 : ℝ) := by norm_num
  have hts : 0 ≤ Cardinal.cantorFunction (1 / 3) f := by
    -- `tsum` of nonnegative terms is nonnegative.
    have hterm : ∀ n, 0 ≤ Cardinal.cantorFunctionAux (1 / 3) f n :=
      fun n => Cardinal.cantorFunctionAux_nonneg (c := (1 / 3 : ℝ)) (f := f) (n := n) h0
    simpa [Cardinal.cantorFunction] using tsum_nonneg hterm
  have hpos : 0 ≤ (2 / 3 : ℝ) := by norm_num
  simpa [cantorEncode] using mul_nonneg hpos hts

theorem cantorEncode_mem_Icc (f : ℕ → Bool) : cantorEncode f ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cantorEncode_nonneg f, cantorEncode_le_one f⟩

theorem encodeTape_mem_Icc (t : Tape) : encodeTape t ∈ Set.Icc (0 : ℝ) 1 :=
  cantorEncode_mem_Icc (digits t)

/-! ### Membership in the ternary Cantor set (by `preCantorSet` recursion) -/

theorem cantorEncode_succ (f : ℕ → Bool) :
    cantorEncode f =
      (if f 0 then (2 + cantorEncode (fun n => f (n + 1))) / 3
       else cantorEncode (fun n => f (n + 1)) / 3) := by
  -- Start from `cantorFunction_succ`.
  have h0 : 0 ≤ (1 / 3 : ℝ) := by norm_num
  have h1 : (1 / 3 : ℝ) < 1 := by norm_num
  have hcf := Cardinal.cantorFunction_succ (c := (1 / 3 : ℝ)) f h0 h1
  unfold cantorEncode
  cases hlead : f 0
  · rw [hcf]
    simp [hlead]
    ring_nf
  · rw [hcf]
    simp [hlead]
    ring_nf

theorem cantorEncode_mem_preCantorSet (f : ℕ → Bool) : ∀ n : ℕ, cantorEncode f ∈ preCantorSet n
  | 0 => by
      simpa [preCantorSet_zero] using cantorEncode_mem_Icc f
  | n + 1 => by
      have ih := cantorEncode_mem_preCantorSet (fun k => f (k + 1)) n
      -- Use the leading digit to choose the left/right component of `preCantorSet (n+1)`.
      have hs := cantorEncode_succ f
      cases hlead : f 0
      · -- leading digit `0`: map is `x ↦ x/3`
        have hs' : cantorEncode f = cantorEncode (fun k => f (k + 1)) / 3 := by
          simpa [hlead] using hs
        refine Or.inl ?_
        refine ⟨cantorEncode (fun k => f (k + 1)), ih, ?_⟩
        simp [hs']
      · -- leading digit `2`: map is `x ↦ (2+x)/3`
        have hs' : cantorEncode f = (2 + cantorEncode (fun k => f (k + 1))) / 3 := by
          simpa [hlead] using hs
        refine Or.inr ?_
        refine ⟨cantorEncode (fun k => f (k + 1)), ih, ?_⟩
        simp [hs']

theorem cantorEncode_mem_cantorSet (f : ℕ → Bool) : cantorEncode f ∈ cantorSet := by
  refine Set.mem_iInter.mpr ?_
  intro n
  exact cantorEncode_mem_preCantorSet f n

theorem encodeTape_mem_cantorSet (t : Tape) : encodeTape t ∈ cantorSet :=
  cantorEncode_mem_cantorSet (digits t)

/-! ## Head-position embedding `τ_k` (paper Lemma 1) -/

/-- The scale used by `τ_k` (always positive): `3^{-(1+|k|)}`. -/
noncomputable def headScale (k : ℤ) : ℝ :=
  ((3 : ℝ) ^ (1 + Int.natAbs k))⁻¹

theorem headScale_pos (k : ℤ) : 0 < headScale k := by
  unfold headScale
  have : 0 < (3 : ℝ) ^ (1 + Int.natAbs k) := by positivity
  exact inv_pos.2 this

/-- The affine embeddings `τ_k : I → I_k` from the paper (with `I = [0,1]`). -/
noncomputable def tau (k : ℤ) (x : ℝ) : ℝ :=
  if k < 0 then
    headScale k * (1 + x)
  else
    1 + headScale k * (-2 + x)

/-- Left endpoint of the head-position interval `I_k`. -/
noncomputable def headLeft (k : ℤ) : ℝ :=
  if k < 0 then headScale k else 1 - 2 * headScale k

/-- Right endpoint of the head-position interval `I_k`. -/
noncomputable def headRight (k : ℤ) : ℝ :=
  if k < 0 then 2 * headScale k else 1 - headScale k

/-- The image interval `I_k` (as a closed interval in `ℝ`). -/
noncomputable def headInterval (k : ℤ) : Set ℝ :=
  Set.Icc (headLeft k) (headRight k)

theorem tau_mem_headInterval {k : ℤ} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    tau k x ∈ headInterval k := by
  have hkpos : 0 < headScale k := headScale_pos k
  have hk0 : 0 ≤ headScale k := le_of_lt hkpos
  by_cases hk : k < 0
  · -- negative branch: `τ_k(x) = s*(1+x)` with `x∈[0,1]`.
    have h1 : (1 : ℝ) ≤ 1 + x := by linarith [hx.1]
    have h2 : 1 + x ≤ (2 : ℝ) := by linarith [hx.2]
    have hlow : headScale k ≤ headScale k * (1 + x) := by
      simpa [one_mul] using mul_le_mul_of_nonneg_left h1 hk0
    have hupp : headScale k * (1 + x) ≤ 2 * headScale k := by
      have := mul_le_mul_of_nonneg_left h2 hk0
      -- rewrite `s*2` as `2*s`
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have ht : tau k x = headScale k * (1 + x) := by simp [tau, hk]
    have hmem : tau k x ∈ Set.Icc (headScale k) (2 * headScale k) := by
      simpa [ht] using (And.intro hlow hupp)
    simpa [headInterval, headLeft, headRight, hk] using hmem
  · -- nonnegative branch: `τ_k(x) = 1 + s*(-2+x)` with `x∈[0,1]`.
    have hxL : (-2 : ℝ) ≤ -2 + x := by linarith [hx.1]
    have hxU : -2 + x ≤ (-1 : ℝ) := by linarith [hx.2]
    have hlow' : headScale k * (-2 : ℝ) ≤ headScale k * (-2 + x) := by
      simpa using mul_le_mul_of_nonneg_left hxL hk0
    have hupp' : headScale k * (-2 + x) ≤ headScale k * (-1 : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hxU hk0
    have hlow : 1 - 2 * headScale k ≤ 1 + headScale k * (-2 + x) := by
      -- add `1` to `hlow'` and normalize.
      have := add_le_add_left hlow' (1 : ℝ)
      -- `1 + s*(-2) = 1 - 2*s`
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, add_assoc] using this
    have hupp : 1 + headScale k * (-2 + x) ≤ 1 - headScale k := by
      have := add_le_add_left hupp' (1 : ℝ)
      -- `1 + s*(-1) = 1 - s`
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, add_assoc] using this
    have ht : tau k x = 1 + headScale k * (-2 + x) := by simp [tau, hk]
    have hmem : tau k x ∈ Set.Icc (1 - 2 * headScale k) (1 - headScale k) := by
      simpa [ht] using (And.intro hlow hupp)
    simpa [headInterval, headLeft, headRight, hk] using hmem

/-! ### Interval properties (paper Theorem 1.4) -/

private theorem negSucc_lt_negSucc_iff (m n : ℕ) :
    (Int.negSucc n : ℤ) < Int.negSucc m ↔ m < n := by
  have hn : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
  have hm : (Int.negSucc m : ℤ) = -((m + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
  constructor
  · intro h
    have : ((m + 1 : ℕ) : ℤ) < ((n + 1 : ℕ) : ℤ) := by
      have h' : -((n + 1 : ℕ) : ℤ) < -((m + 1 : ℕ) : ℤ) := by simpa [hn, hm] using h
      exact (Int.neg_lt_neg_iff).1 h'
    have : m + 1 < n + 1 := (Int.ofNat_lt).1 this
    exact Nat.lt_of_add_lt_add_right this
  · intro hmn
    have : ((m + 1 : ℕ) : ℤ) < ((n + 1 : ℕ) : ℤ) := (Int.ofNat_lt).2 (Nat.succ_lt_succ hmn)
    have : -((n + 1 : ℕ) : ℤ) < -((m + 1 : ℕ) : ℤ) := (Int.neg_lt_neg_iff).2 this
    simpa [hn, hm] using this

private lemma pow3_gt_two (d : ℕ) (hd : d ≠ 0) : (2 : ℝ) < (3 : ℝ) ^ d := by
  have h23 : (2 : ℝ) < (3 : ℝ) := by norm_num
  have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ d := by
    have h13 : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
    exact le_self_pow₀ h13 hd
  exact lt_of_lt_of_le h23 h3

private lemma pow_mul_inv_pow_add (m d : ℕ) :
    ((3 : ℝ) ^ d) * ((3 : ℝ) ^ (m + d))⁻¹ = ((3 : ℝ) ^ m)⁻¹ := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hd0 : ((3 : ℝ) ^ d) ≠ 0 := pow_ne_zero d h3
  calc
    (3 : ℝ) ^ d * ((3 : ℝ) ^ (m + d))⁻¹ = (3 : ℝ) ^ d / (3 : ℝ) ^ (m + d) := by
      simp [div_eq_mul_inv]
    _ = (3 : ℝ) ^ d / ((3 : ℝ) ^ m * (3 : ℝ) ^ d) := by
      simp [pow_add]
    _ = (1 : ℝ) / (3 : ℝ) ^ m := by
      simpa [one_mul] using
        (mul_div_mul_right (a := (1 : ℝ)) (b := (3 : ℝ) ^ m) (c := (3 : ℝ) ^ d) hd0)
    _ = ((3 : ℝ) ^ m)⁻¹ := by simp

private lemma two_mul_inv_pow_lt_inv_pow_of_lt_add (c m n : ℕ) (h : m < n) :
    (2 : ℝ) * ((3 : ℝ) ^ (n + c))⁻¹ < ((3 : ℝ) ^ (m + c))⁻¹ := by
  let d : ℕ := n - m
  have hd0 : d ≠ 0 := Nat.sub_ne_zero_of_lt h
  have hn : m + d = n := Nat.add_sub_cancel' (Nat.le_of_lt h)
  have hpow : (2 : ℝ) < (3 : ℝ) ^ d := pow3_gt_two d hd0
  have hspos : 0 < ((3 : ℝ) ^ (n + c))⁻¹ := by
    have : 0 < (3 : ℝ) ^ (n + c) := by positivity
    exact inv_pos.2 this
  have hmul :
      (2 : ℝ) * ((3 : ℝ) ^ (n + c))⁻¹ < (3 : ℝ) ^ d * ((3 : ℝ) ^ (n + c))⁻¹ :=
    mul_lt_mul_of_pos_right hpow hspos
  have hrhs : (3 : ℝ) ^ d * ((3 : ℝ) ^ (n + c))⁻¹ = ((3 : ℝ) ^ (m + c))⁻¹ := by
    have hnc : n + c = (m + c) + d := by
      have : n = m + d := hn.symm
      calc
        n + c = (m + d) + c := by simp [this]
        _ = (m + c) + d := by
          simp [Nat.add_assoc, Nat.add_comm]
    calc
      (3 : ℝ) ^ d * ((3 : ℝ) ^ (n + c))⁻¹ = (3 : ℝ) ^ d * ((3 : ℝ) ^ ((m + c) + d))⁻¹ := by
        simp [hnc]
      _ = ((3 : ℝ) ^ (m + c))⁻¹ := by
        simpa [Nat.add_assoc] using pow_mul_inv_pow_add (m := (m + c)) (d := d)
  simpa [hrhs] using hmul

theorem headInterval_length (k : ℤ) : headRight k - headLeft k = headScale k := by
  by_cases hk : k < 0 <;> simp [headLeft, headRight, hk] <;> ring_nf

theorem headRight_lt_headLeft_of_lt {k k' : ℤ} (h : k < k') : headRight k < headLeft k' := by
  cases k with
  | ofNat n =>
    cases k' with
    | ofNat m =>
      have hnm : n < m := (Int.ofNat_lt).1 h
      have hscale : (2 : ℝ) * ((3 : ℝ) ^ (m + 1))⁻¹ < ((3 : ℝ) ^ (n + 1))⁻¹ :=
        two_mul_inv_pow_lt_inv_pow_of_lt_add (c := 1) (m := n) (n := m) hnm
      have hscale' : 2 * headScale (Int.ofNat m) < headScale (Int.ofNat n) := by
        simpa [headScale, Nat.add_comm] using hscale
      have hn0 : ¬((n : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg n)
      have hm0 : ¬((m : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg m)
      -- `1 - s_n < 1 - 2*s_m`
      simpa [headLeft, headRight, hn0, hm0] using sub_lt_sub_left hscale' (1 : ℝ)
    | negSucc m =>
      exfalso
      have h0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      have hneg : (Int.negSucc m : ℤ) < 0 := Int.negSucc_lt_zero m
      have : (0 : ℤ) < Int.negSucc m := lt_of_le_of_lt h0 h
      exact (not_lt_of_gt hneg) this
  | negSucc n =>
    cases k' with
    | negSucc m =>
      have hmn : m < n := (negSucc_lt_negSucc_iff (m := m) (n := n)).1 h
      have hscale :
          (2 : ℝ) * ((3 : ℝ) ^ (n + 2))⁻¹ < ((3 : ℝ) ^ (m + 2))⁻¹ :=
        two_mul_inv_pow_lt_inv_pow_of_lt_add (c := 2) (m := m) (n := n) hmn
      simpa [headLeft, headRight, headScale, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hscale
    | ofNat m =>
      -- negative interval is left of every nonnegative interval (uniform bounds).
      have hn2 : (2 : ℕ) ≤ n + 2 := Nat.le_add_left 2 n
      have hm1 : (1 : ℕ) ≤ m + 1 := Nat.le_add_left 1 m
      have h13 : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
      have hpowN : (3 : ℝ) ^ 2 ≤ (3 : ℝ) ^ (n + 2) := pow_le_pow_right₀ h13 hn2
      have hpowM : (3 : ℝ) ^ 1 ≤ (3 : ℝ) ^ (m + 1) := pow_le_pow_right₀ h13 hm1
      have hNpos : 0 < (3 : ℝ) ^ 2 := by positivity
      have hMpos : 0 < (3 : ℝ) ^ 1 := by positivity
      have hscaleN : ((3 : ℝ) ^ (n + 2))⁻¹ ≤ ((3 : ℝ) ^ 2)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hNpos hpowN
      have hscaleM : ((3 : ℝ) ^ (m + 1))⁻¹ ≤ ((3 : ℝ) ^ 1)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hMpos hpowM
      have hRle' : 2 * headScale (Int.negSucc n) ≤ 2 * ((3 : ℝ) ^ 2)⁻¹ := by
        have : 2 * ((3 : ℝ) ^ (n + 2))⁻¹ ≤ 2 * ((3 : ℝ) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hscaleN (by norm_num)
        simpa [headScale, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      have hRle : 2 * headScale (Int.negSucc n) ≤ (2 / 9 : ℝ) := by
        have h23 : (2 : ℝ) * ((3 : ℝ) ^ 2)⁻¹ = (2 / 9 : ℝ) := by norm_num
        simpa [h23] using hRle'
      have hLge : (1 / 3 : ℝ) ≤ headLeft (Int.ofNat m) := by
        have hm0 : ¬((m : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg m)
        have : 2 * ((3 : ℝ) ^ (m + 1))⁻¹ ≤ 2 * ((3 : ℝ) ^ 1)⁻¹ :=
          mul_le_mul_of_nonneg_left hscaleM (by norm_num)
        have : 1 - 2 * ((3 : ℝ) ^ (m + 1))⁻¹ ≥ 1 - 2 * ((3 : ℝ) ^ 1)⁻¹ :=
          sub_le_sub_left this (1 : ℝ)
        have h' : 1 - 2 * ((3 : ℝ) ^ 1)⁻¹ ≤ 1 - 2 * ((3 : ℝ) ^ (m + 1))⁻¹ := this
        have hbase : (1 / 3 : ℝ) = 1 - 2 * ((3 : ℝ) ^ 1)⁻¹ := by norm_num
        -- `1/3 = 1 - 2/3` and `headLeft (ofNat m) = 1 - 2*headScale (ofNat m)`.
        simpa [headLeft, headScale, hm0, Nat.add_comm, hbase] using h'
      have hsep : (2 / 9 : ℝ) < (1 / 3 : ℝ) := by norm_num
      -- chain: headRight k ≤ 2/9 < 1/3 ≤ headLeft k'
      have : headRight (Int.negSucc n) < headLeft (Int.ofNat m) := by
        have hR : headRight (Int.negSucc n) ≤ (2 / 9 : ℝ) := by
          simpa [headRight, headScale, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hRle
        exact lt_of_le_of_lt hR (lt_of_lt_of_le hsep hLge)
      exact this

private theorem disjoint_Icc_of_lt {a b c d : ℝ} (h : b < c) : Disjoint (Set.Icc a b) (Set.Icc c d) := by
  refine Set.disjoint_left.2 ?_
  intro x hx1 hx2
  have hcb : c ≤ b := le_trans hx2.1 hx1.2
  exact (not_le_of_gt h) hcb

theorem headInterval_disjoint (k k' : ℤ) (h : k ≠ k') : Disjoint (headInterval k) (headInterval k') := by
  have hlt : k < k' ∨ k' < k := lt_or_gt_of_ne h
  rcases hlt with hlt | hgt
  · exact disjoint_Icc_of_lt (headRight_lt_headLeft_of_lt hlt)
  · simpa [disjoint_comm] using disjoint_Icc_of_lt (headRight_lt_headLeft_of_lt hgt)

theorem headInterval_lt_of_lt {k k' : ℤ} (h : k < k') {x y : ℝ}
    (hx : x ∈ headInterval k) (hy : y ∈ headInterval k') : x < y := by
  have hsep : headRight k < headLeft k' := headRight_lt_headLeft_of_lt h
  have hxR : x ≤ headRight k := hx.2
  have hyL : headLeft k' ≤ y := hy.1
  exact lt_of_le_of_lt hxR (lt_of_lt_of_le hsep hyL)

theorem headScale_neg (k : ℤ) : headScale (-k) = headScale k := by
  simp [headScale, Int.natAbs_neg]

theorem headLeft_neg (k : ℤ) : headLeft (-k) = 1 - headRight k := by
  have hs : headScale (-k) = headScale k := headScale_neg k
  by_cases hk : k < 0
  · have hnegk : ¬(-k < 0) := by
      intro h
      have : 0 < k := (neg_lt_zero).1 h
      exact (not_lt_of_ge (le_of_lt hk)) this
    unfold headLeft headRight
    rw [if_neg hnegk]
    rw [if_pos hk]
    simp [hs]
  · have hk' : ¬(k < 0) := hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [headLeft, headRight, headScale]
      ring_nf
    · have hkpos : 0 < k := lt_of_le_of_ne (le_of_not_gt hk') (Ne.symm hk0)
      have hnegk : (-k < 0) := neg_neg_of_pos hkpos
      unfold headLeft headRight
      rw [if_pos hnegk]
      rw [if_neg hk']
      simp [hs]

theorem headRight_neg (k : ℤ) : headRight (-k) = 1 - headLeft k := by
  have hs : headScale (-k) = headScale k := headScale_neg k
  by_cases hk : k < 0
  · have hnegk : ¬(-k < 0) := by
      intro h
      have : 0 < k := (neg_lt_zero).1 h
      exact (not_lt_of_ge (le_of_lt hk)) this
    unfold headLeft headRight
    rw [if_neg hnegk]
    rw [if_pos hk]
    simp [hs]
  · have hk' : ¬(k < 0) := hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [headLeft, headRight, headScale]
      ring_nf
    · have hkpos : 0 < k := lt_of_le_of_ne (le_of_not_gt hk') (Ne.symm hk0)
      have hnegk : (-k < 0) := neg_neg_of_pos hkpos
      unfold headLeft headRight
      rw [if_pos hnegk]
      rw [if_neg hk']
      simp [hs]

/-- Reflection symmetry about `1/2` for the interval family `I_k` (the paper’s “symmetry”). -/
theorem headInterval_reflect (k : ℤ) {x : ℝ} :
    x ∈ headInterval k ↔ (1 - x) ∈ headInterval (-k) := by
  unfold headInterval
  simp [headLeft_neg, headRight_neg]
  constructor
  · rintro ⟨hxL, hxU⟩
    constructor <;> linarith
  · rintro ⟨hxL, hxU⟩
    constructor <;> linarith

/-! ### Shift law (paper Lemma 1) -/

theorem tau_shift_law (k : ℤ) (x : ℝ) :
    tau (k + 1) x =
      (if k < 0 then 3 * tau k x else tau k x / 3 + 2 / 3) := by
  cases k with
  | ofNat n =>
    -- `k = n ≥ 0`, so we are in the `k ≥ 0` branch.
    have hk0 : ¬((n : ℤ) < 0) := not_lt_of_ge (Int.natCast_nonneg n)
    have hk1 : ¬((1 : ℤ) + (n : ℤ) < 0) := by
      have : (0 : ℤ) ≤ (1 : ℤ) + (n : ℤ) :=
        add_nonneg (show (0 : ℤ) ≤ 1 by decide) (Int.natCast_nonneg n)
      exact not_lt_of_ge this
    have hrew : ((n : ℤ) + 1) = (1 : ℤ) + (n : ℤ) := by simp [add_comm]
    have hnabs : (1 + (n : ℤ)).natAbs = n + 1 := by
      have h : (1 + (n : ℤ)) = ((n + 1 : ℕ) : ℤ) := by simp [add_comm]
      rw [h]
      simpa using (Int.natAbs_natCast (n + 1))
    simp [tau, headScale, hk0, hk1, hrew, hnabs, Nat.add_comm]
    ring_nf
  | negSucc n =>
    -- `k < 0`, so we are in the `k < 0` branch.
    have hk : (Int.negSucc n : ℤ) < 0 := Int.negSucc_lt_zero n
    cases n with
    | zero =>
      -- `k = -1`, `k+1 = 0`.
      simp [tau, headScale]
      ring_nf
    | succ m =>
      -- `k = -(m+2)`, `k+1 = -(m+1)`.
      have hrew : (Int.negSucc (Nat.succ m) + 1 : ℤ) = Int.negSucc m := by
        simp [Int.negSucc_eq]
      simp [tau, headScale, hrew, Nat.add_comm]
      ring_nf

/-- The combined encoding `x_{t,k} := τ_k(x_t)` from the paper. -/
noncomputable def encodeWithHead (t : Tape) (k : ℤ) : ℝ :=
  tau k (encodeTape t)

theorem encodeWithHead_shift (t : Tape) (k : ℤ) :
    encodeWithHead t (k + 1) =
      (if k < 0 then 3 * encodeWithHead t k else encodeWithHead t k / 3 + 2 / 3) := by
  simpa [encodeWithHead] using tau_shift_law k (encodeTape t)

/-! ### Injectivity (lossless combined encoding) -/

theorem tau_injective (k : ℤ) : Function.Injective (tau k) := by
  intro x y hxy
  have hs0 : headScale k ≠ 0 := by
    exact ne_of_gt (headScale_pos k)
  by_cases hk : k < 0
  · have h' : headScale k * (1 + x) = headScale k * (1 + y) := by
      simpa [tau, hk] using hxy
    have h1 : (1 + x) = (1 + y) :=
      (mul_left_cancel₀ hs0) h'
    linarith
  · have h' : 1 + headScale k * (-2 + x) = 1 + headScale k * (-2 + y) := by
      simpa [tau, hk] using hxy
    have hmul : headScale k * (-2 + x) = headScale k * (-2 + y) :=
      add_left_cancel h'
    have hadd : (-2 + x) = (-2 + y) :=
      (mul_left_cancel₀ hs0) hmul
    linarith

theorem encodeWithHead_injective : Function.Injective (fun p : Tape × ℤ => encodeWithHead p.1 p.2) := by
  intro p q hpq
  rcases p with ⟨t, k⟩
  rcases q with ⟨t', k'⟩
  have hk : k = k' := by
    by_contra hne
    have hx : encodeWithHead t k ∈ headInterval k :=
      tau_mem_headInterval (k := k) (x := encodeTape t) (encodeTape_mem_Icc t)
    have hx' : encodeWithHead t k ∈ headInterval k' := by
      have hy : encodeWithHead t' k' ∈ headInterval k' :=
        tau_mem_headInterval (k := k') (x := encodeTape t') (encodeTape_mem_Icc t')
      simpa [hpq] using hy
    have hd : Disjoint (headInterval k) (headInterval k') :=
      headInterval_disjoint k k' hne
    exact (Set.disjoint_left.1 hd) hx hx'
  subst hk
  have htape : t = t' := by
    have h0 : tau k (encodeTape t) = tau k (encodeTape t') := by
      simpa [encodeWithHead] using hpq
    have h1 : encodeTape t = encodeTape t' :=
      tau_injective k h0
    exact encodeTape_injective h1
  subst htape
  rfl

end Billiards
end MirandaDynamics
end HeytingLean
