import HeytingLean.Analysis.RZ.Interval

namespace HeytingLean
namespace Analysis
namespace RZ

/-!
# RZ: exact reals as nested dyadic intervals (scaffolding)

This file lifts the dyadic interval arithmetic layer to a simple “exact real” representation:

* an exact real is given by a monotone (information-increasing) sequence of intervals
  whose widths are bounded by `2^{-n}`.

This mirrors the classic interval-domain presentation used in constructive exact real arithmetic
(e.g. Bauer’s “reals via interval arithmetic” expositions), while keeping the carrier purely `ℚ`.
-/

open Interval

/-- An “exact real” represented by a chain of shrinking rational intervals. -/
structure ExactReal where
  approx : Nat → Interval
  mono : Monotone approx
  width_bound : ∀ n, (approx n).width ≤ 1 / pow2 n

namespace ExactReal

@[simp] lemma width_bound' (x : ExactReal) (n : Nat) : (x.approx n).width ≤ 1 / pow2 n :=
  x.width_bound n

/-- Embed a rational as a degenerate exact real. -/
def ofRat (q : ℚ) : ExactReal :=
  { approx := fun _ => Interval.ofRat q
    mono := by
      intro _ _ _
      exact le_rfl
    width_bound := by
      intro n
      -- width is 0, and `1 / 2^n` is nonnegative
      have hnonneg : (0 : ℚ) ≤ (1 : ℚ) / pow2 n := by
        exact div_nonneg (by norm_num) (le_of_lt (pow2_pos n))
      simpa [Interval.width, Interval.ofRat] using hnonneg }

private lemma pow2_add_two (n : Nat) : pow2 (n + 2) = pow2 n * (4 : ℚ) := by
  dsimp [pow2]
  calc
    (2 : ℚ) ^ (n + 2) = (2 : ℚ) ^ n * (2 : ℚ) ^ 2 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (pow_add (2 : ℚ) n 2)
    _ = (2 : ℚ) ^ n * (4 : ℚ) := by
      norm_num

private lemma add_width_budget (n : Nat) :
    (1 : ℚ) / pow2 (n + 2) + (1 : ℚ) / pow2 (n + 2) + (2 : ℚ) / pow2 (n + 2) = (1 : ℚ) / pow2 n := by
  have h : pow2 (n + 2) = pow2 n * (4 : ℚ) := pow2_add_two n
  field_simp [h, pow2_ne0]
  ring_nf
  -- remaining goal is exactly the `pow2` identity
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h.symm

/-- Addition of exact reals via dyadic-rounded interval addition. -/
def add (x y : ExactReal) : ExactReal :=
  { approx := fun n => Interval.add (n + 2) (x.approx (n + 2)) (y.approx (n + 2))
    mono := by
      apply monotone_nat_of_le_succ
      intro n
      -- Step `n → n+1` uses more precise input intervals and one more rounding bit.
      have hx : x.approx (n + 2) ≤ x.approx (n + 3) :=
        x.mono (Nat.le_succ (n + 2))
      have hy : y.approx (n + 2) ≤ y.approx (n + 3) :=
        y.mono (Nat.le_succ (n + 2))
      have hArg :
          Interval.add (n + 2) (x.approx (n + 2)) (y.approx (n + 2))
            ≤ Interval.add (n + 2) (x.approx (n + 3)) (y.approx (n + 3)) :=
        Interval.add_mono hx hy
      have hPrec :
          Interval.add (n + 2) (x.approx (n + 3)) (y.approx (n + 3))
            ≤ Interval.add (n + 3) (x.approx (n + 3)) (y.approx (n + 3)) :=
        Interval.add_mono_precision_succ (n + 2) (x.approx (n + 3)) (y.approx (n + 3))
      exact le_trans hArg hPrec
    width_bound := by
      intro n
      have h0 :
          (Interval.add (n + 2) (x.approx (n + 2)) (y.approx (n + 2))).width
            ≤ (x.approx (n + 2)).width + (y.approx (n + 2)).width + 2 / pow2 (n + 2) :=
        Interval.width_add_le (n + 2) (x.approx (n + 2)) (y.approx (n + 2))
      have hx : (x.approx (n + 2)).width ≤ 1 / pow2 (n + 2) := x.width_bound (n + 2)
      have hy : (y.approx (n + 2)).width ≤ 1 / pow2 (n + 2) := y.width_bound (n + 2)
      have hxy : (x.approx (n + 2)).width + (y.approx (n + 2)).width
          ≤ (1 : ℚ) / pow2 (n + 2) + (1 : ℚ) / pow2 (n + 2) :=
        add_le_add hx hy
      have hxyz :
          (x.approx (n + 2)).width + (y.approx (n + 2)).width + 2 / pow2 (n + 2)
            ≤ (1 : ℚ) / pow2 (n + 2) + (1 : ℚ) / pow2 (n + 2) + (2 : ℚ) / pow2 (n + 2) :=
        add_le_add_right hxy (2 / pow2 (n + 2))
      calc
        (Interval.add (n + 2) (x.approx (n + 2)) (y.approx (n + 2))).width
            ≤ (x.approx (n + 2)).width + (y.approx (n + 2)).width + 2 / pow2 (n + 2) := h0
        _ ≤ (1 : ℚ) / pow2 (n + 2) + (1 : ℚ) / pow2 (n + 2) + (2 : ℚ) / pow2 (n + 2) := hxyz
        _ = (1 : ℚ) / pow2 n := add_width_budget n }

/-- Negation of exact reals (exact on intervals). -/
def neg (x : ExactReal) : ExactReal :=
  { approx := fun n => Interval.neg (x.approx n)
    mono := by
      intro a b hab
      exact Interval.neg_mono (x.mono hab)
    width_bound := by
      intro n
      simpa [Interval.width_neg] using x.width_bound n }

/-- Subtraction: `x - y := x + (-y)`. -/
def sub (x y : ExactReal) : ExactReal :=
  add x (neg y)

/-! ## Canonical rational approximation (midpoints) -/

/-- Midpoint of an interval. -/
def midpoint (I : Interval) : ℚ := (I.lo + I.hi) / 2

lemma midpoint_mem (I : Interval) : midpoint I ∈ I := by
  have h2 : (0 : ℚ) < 2 := by norm_num
  constructor
  · have h : I.lo + I.lo ≤ I.lo + I.hi := add_le_add_left I.lo_le_hi I.lo
    have h' : I.lo * 2 ≤ I.lo + I.hi := by
      simpa [mul_two] using h
    have := (le_div_iff₀ h2).2 h'
    simpa [midpoint, add_assoc, add_left_comm, add_comm] using this
  · have h : I.lo + I.hi ≤ I.hi + I.hi := add_le_add_right I.lo_le_hi I.hi
    have h' : I.lo + I.hi ≤ I.hi * 2 := by
      simpa [mul_two] using h
    have := (div_le_iff₀ h2).2 h'
    simpa [midpoint, add_assoc, add_left_comm, add_comm] using this

lemma abs_sub_le_width {I : Interval} {x y : ℚ} (hx : x ∈ I) (hy : y ∈ I) :
    |x - y| ≤ I.width := by
  apply (abs_sub_le_iff (a := x) (b := y) (c := I.width)).2
  constructor
  · have h1 : x - y ≤ I.hi - y := sub_le_sub_right hx.2 y
    have h2 : I.hi - y ≤ I.hi - I.lo := by
      have : -y ≤ -I.lo := neg_le_neg hy.1
      have := add_le_add_left this I.hi
      simpa [sub_eq_add_neg, add_assoc] using this
    exact le_trans h1 (by simpa [Interval.width] using h2)
  · have h1 : y - x ≤ I.hi - x := sub_le_sub_right hy.2 x
    have h2 : I.hi - x ≤ I.hi - I.lo := by
      have : -x ≤ -I.lo := neg_le_neg hx.1
      have := add_le_add_left this I.hi
      simpa [sub_eq_add_neg, add_assoc] using this
    exact le_trans h1 (by simpa [Interval.width] using h2)

/-- A canonical rational “sample” for an exact real at precision `n`. -/
def sample (x : ExactReal) (n : Nat) : ℚ :=
  midpoint (x.approx n)

lemma sample_mem (x : ExactReal) (n : Nat) : sample x n ∈ x.approx n :=
  midpoint_mem (x.approx n)

/-- The midpoint samples form a fast Cauchy sequence (witnessed by the interval widths). -/
lemma abs_sub_sample_le (x : ExactReal) {m n : Nat} (hmn : m ≤ n) :
    |sample x m - sample x n| ≤ 1 / pow2 m := by
  have hmn' : x.approx m ≤ x.approx n := x.mono hmn
  have hsub : (x.approx n).toSet ⊆ (x.approx m).toSet :=
    (Interval.le_iff_subset).1 hmn'
  have hm : sample x m ∈ x.approx m := sample_mem x m
  have hn : sample x n ∈ x.approx m := hsub (sample_mem x n)
  have habs : |sample x m - sample x n| ≤ (x.approx m).width :=
    abs_sub_le_width (I := x.approx m) hm hn
  exact le_trans habs (x.width_bound m)

end ExactReal

end RZ
end Analysis
end HeytingLean
