import Mathlib.Data.Rat.Floor

namespace HeytingLean
namespace Analysis
namespace RZ

/-!
# RZ: dyadic rounding on `ℚ`

This module provides simple “RZ-style” dyadic rounding operators on rationals:

* `roundDown p q` — a dyadic rational (denominator `2^p`) with `roundDown p q ≤ q`
* `roundUp p q` — a dyadic rational (denominator `2^p`) with `q ≤ roundUp p q`

This is intended to be the numeric core used by interval arithmetic in `RZ.Interval`.
We keep the carrier as `ℚ` to avoid a heavy normalization layer early on; dyadic-ness
is controlled by the precision parameter `p`.
-/

/-- The rational `2^p`. -/
def pow2 (p : Nat) : ℚ := (2 : ℚ) ^ p

lemma pow2_pos (p : Nat) : (0 : ℚ) < pow2 p := by
  dsimp [pow2]
  exact pow_pos zero_lt_two p

lemma pow2_ne0 (p : Nat) : pow2 p ≠ (0 : ℚ) :=
  ne_of_gt (pow2_pos p)

/-- Round `q` *down* to the dyadic grid of step `2^{-p}`. -/
def roundDown (p : Nat) (q : ℚ) : ℚ :=
  (Rat.floor (q * pow2 p) : ℚ) / pow2 p

/-- Round `q` *up* to the dyadic grid of step `2^{-p}`. -/
def roundUp (p : Nat) (q : ℚ) : ℚ :=
  - roundDown p (-q)

lemma roundDown_lt_add_one_div_pow2 (p : Nat) (q : ℚ) : q < roundDown p q + 1 / pow2 p := by
  unfold roundDown
  have hp : (0 : ℚ) < pow2 p := pow2_pos p
  have hlt : q * pow2 p < (⌊q * pow2 p⌋ : ℚ) + 1 := by
    exact Int.lt_floor_add_one (q * pow2 p)
  have hdiv := div_lt_div_of_pos_right hlt hp
  -- clear denominators
  simpa [pow2_ne0, mul_div_cancel_right₀, add_div] using hdiv

lemma sub_one_div_pow2_le_roundDown (p : Nat) (q : ℚ) : q - 1 / pow2 p ≤ roundDown p q := by
  have h : q < roundDown p q + 1 / pow2 p := roundDown_lt_add_one_div_pow2 p q
  have h' : q - 1 / pow2 p < roundDown p q :=
    (sub_lt_iff_lt_add).2 h
  exact le_of_lt h'

lemma roundUp_le_add_one_div_pow2 (p : Nat) (q : ℚ) : roundUp p q ≤ q + 1 / pow2 p := by
  unfold roundUp
  have h : (-q) - 1 / pow2 p ≤ roundDown p (-q) :=
    sub_one_div_pow2_le_roundDown p (-q)
  have hneg : -roundDown p (-q) ≤ -((-q) - 1 / pow2 p) :=
    neg_le_neg h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg

lemma roundDown_le (p : Nat) (q : ℚ) : roundDown p q ≤ q := by
  unfold roundDown
  have h : (Rat.floor (q * pow2 p) : ℚ) ≤ q * pow2 p :=
    Rat.floor_le (a := q * pow2 p)
  have hp : (0 : ℚ) ≤ pow2 p := le_of_lt (pow2_pos p)
  have hdiv : (Rat.floor (q * pow2 p) : ℚ) / pow2 p ≤ q * pow2 p / pow2 p :=
    div_le_div_of_nonneg_right h hp
  calc
    (Rat.floor (q * pow2 p) : ℚ) / pow2 p ≤ q * pow2 p / pow2 p := hdiv
    _ = q := by simp [pow2_ne0, mul_div_cancel_right₀]

lemma le_roundUp (p : Nat) (q : ℚ) : q ≤ roundUp p q := by
  unfold roundUp
  have h : roundDown p (-q) ≤ -q := roundDown_le p (-q)
  have hneg : -(-q) ≤ -(roundDown p (-q)) := neg_le_neg h
  simpa using hneg

lemma pow2_succ (p : Nat) : pow2 (p + 1) = pow2 p * 2 := by
  simp [pow2, pow_succ]

lemma roundDown_le_succ (p : Nat) (q : ℚ) : roundDown p q ≤ roundDown (p + 1) q := by
  unfold roundDown
  have hp1 : (0 : ℚ) < pow2 (p + 1) := pow2_pos (p + 1)
  have hpow : pow2 (p + 1) = pow2 p * 2 := pow2_succ p

  have hm_le : ((Rat.floor (q * pow2 p) : ℤ) : ℚ) ≤ q * pow2 p := by
    simpa using (Rat.floor_le (a := q * pow2 p))

  have hmul2 : ((2 : ℚ) * ((Rat.floor (q * pow2 p) : ℤ) : ℚ)) ≤ (2 : ℚ) * (q * pow2 p) :=
    mul_le_mul_of_nonneg_left hm_le (by norm_num)

  have hcast : ((2 * Rat.floor (q * pow2 p) : ℤ) : ℚ) ≤ q * pow2 (p + 1) := by
    simpa [hpow, mul_assoc, mul_left_comm, mul_comm] using hmul2

  have hfloor : (2 * Rat.floor (q * pow2 p)) ≤ Rat.floor (q * pow2 (p + 1)) :=
    (Rat.le_floor_iff (x := (2 * Rat.floor (q * pow2 p))) (a := q * pow2 (p + 1))).2 hcast

  have hfloorRat : ((2 * Rat.floor (q * pow2 p) : ℤ) : ℚ) ≤ (Rat.floor (q * pow2 (p + 1)) : ℚ) :=
    (Int.cast_le (R := ℚ)).2 hfloor

  have hdiv :
      ((2 * Rat.floor (q * pow2 p) : ℤ) : ℚ) / pow2 (p + 1)
        ≤ (Rat.floor (q * pow2 (p + 1)) : ℚ) / pow2 (p + 1) :=
    div_le_div_of_nonneg_right hfloorRat (le_of_lt hp1)

  -- rewrite denom and cancel the common factor `2`
  have hdiv' :
      ((2 * Rat.floor (q * pow2 p) : ℤ) : ℚ) / (pow2 p * 2)
        ≤ (Rat.floor (q * (pow2 p * 2)) : ℚ) / (pow2 p * 2) := by
    simpa [hpow] using hdiv

  have hdiv'' :
      ((Rat.floor (q * pow2 p) : ℚ) * (2 : ℚ)) / (pow2 p * 2)
        ≤ (Rat.floor (q * (pow2 p * 2)) : ℚ) / (pow2 p * 2) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv'

  have hcancel :
      (Rat.floor (q * pow2 p) : ℚ) / pow2 p
        ≤ (Rat.floor (q * (pow2 p * 2)) : ℚ) / (pow2 p * 2) := by
    simpa [mul_div_mul_right, (by norm_num : (2 : ℚ) ≠ 0)] using hdiv''

  simpa [hpow] using hcancel

lemma roundUp_succ_le (p : Nat) (q : ℚ) : roundUp (p + 1) q ≤ roundUp p q := by
  unfold roundUp
  have h : roundDown p (-q) ≤ roundDown (p + 1) (-q) :=
    roundDown_le_succ p (-q)
  have hneg : -roundDown (p + 1) (-q) ≤ -roundDown p (-q) :=
    neg_le_neg h
  simpa using hneg

lemma roundDown_mono (p : Nat) : Monotone (roundDown p) := by
  intro a b hab
  unfold roundDown
  have hp : (0 : ℚ) ≤ pow2 p := le_of_lt (pow2_pos p)
  have hmul : a * pow2 p ≤ b * pow2 p :=
    mul_le_mul_of_nonneg_right hab hp
  have hInt : Rat.floor (a * pow2 p) ≤ Rat.floor (b * pow2 p) :=
    Rat.floor_monotone hmul
  have hRat : (Rat.floor (a * pow2 p) : ℚ) ≤ (Rat.floor (b * pow2 p) : ℚ) :=
    (Int.cast_le (R := ℚ)).2 hInt
  exact div_le_div_of_nonneg_right hRat hp

lemma roundUp_mono (p : Nat) : Monotone (roundUp p) := by
  intro a b hab
  unfold roundUp
  have h : roundDown p (-b) ≤ roundDown p (-a) :=
    roundDown_mono p (neg_le_neg hab)
  have hneg : -(roundDown p (-a)) ≤ -(roundDown p (-b)) := neg_le_neg h
  simpa using hneg

lemma roundDown_le_roundUp (p : Nat) (q : ℚ) : roundDown p q ≤ roundUp p q :=
  (roundDown_le p q).trans (le_roundUp p q)

/-! ## “Approximation operators” for arithmetic -/

def addApproxDown (p : Nat) (x y : ℚ) : ℚ := roundDown p (x + y)
def addApproxUp (p : Nat) (x y : ℚ) : ℚ := roundUp p (x + y)

def mulApproxDown (p : Nat) (x y : ℚ) : ℚ := roundDown p (x * y)
def mulApproxUp (p : Nat) (x y : ℚ) : ℚ := roundUp p (x * y)

lemma addApproxDown_le (p : Nat) (x y : ℚ) : addApproxDown p x y ≤ x + y :=
  roundDown_le p (x + y)

lemma le_addApproxUp (p : Nat) (x y : ℚ) : x + y ≤ addApproxUp p x y :=
  le_roundUp p (x + y)

lemma mulApproxDown_le (p : Nat) (x y : ℚ) : mulApproxDown p x y ≤ x * y :=
  roundDown_le p (x * y)

lemma le_mulApproxUp (p : Nat) (x y : ℚ) : x * y ≤ mulApproxUp p x y :=
  le_roundUp p (x * y)

end RZ
end Analysis
end HeytingLean
