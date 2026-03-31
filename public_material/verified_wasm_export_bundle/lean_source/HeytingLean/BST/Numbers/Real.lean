import Mathlib
import HeytingLean.BST.Numbers.Rat

/-!
# BST.Numbers.Real

Finite-grid real approximation layer.

`RealB k` is a finite grid with denominator `k^2` and numerator in `[-k^2, k^2]`.
Operations are defined by exact rational computation followed by explicit rounding
back to the grid via finite search.
-/

namespace HeytingLean.BST

def RealRadius (k : ℕ) : ℕ := k ^ 2

abbrev RealB (k : ℕ) := Fin (2 * RealRadius k + 1)

namespace RealB

def halfStep (k : ℕ) : Rat :=
  ((1 : Rat) / 2) / ((RealRadius k : ℕ) : Rat)

def default (k : ℕ) : RealB k :=
  ⟨RealRadius k, by
    dsimp [RealRadius]
    omega⟩

def candidates (k : ℕ) : List (RealB k) :=
  List.finRange (2 * RealRadius k + 1)

def toInt {k : ℕ} (x : RealB k) : Int :=
  (x.1 : Int) - (RealRadius k : Int)

def toRat {k : ℕ} (_hk : 0 < k) (x : RealB k) : Rat :=
  ((toInt x : Int) : Rat) / ((RealRadius k : ℕ) : Rat)

def distance {k : ℕ} (hk : 0 < k) (x : RealB k) (q : Rat) : Rat :=
  |toRat hk x - q|

def round {k : ℕ} (hk : 0 < k) (q : Rat) : RealB k :=
  ((candidates k).argmin (fun x => distance hk x q)).getD (default k)

def neg {k : ℕ} (hk : 0 < k) (x : RealB k) : RealB k :=
  round hk (-toRat hk x)

def add {k : ℕ} (hk : 0 < k) (x y : RealB k) : RealB k :=
  round hk (toRat hk x + toRat hk y)

def sub {k : ℕ} (hk : 0 < k) (x y : RealB k) : RealB k :=
  round hk (toRat hk x - toRat hk y)

def mul {k : ℕ} (hk : 0 < k) (x y : RealB k) : RealB k :=
  round hk (toRat hk x * toRat hk y)

def approxEq {k : ℕ} (hk : 0 < k) (ε : Rat) (x y : RealB k) : Prop :=
  |toRat hk x - toRat hk y| ≤ ε

def ofInt (k : ℕ) (z : Int)
    (hzl : -(RealRadius k : Int) ≤ z) (hzu : z ≤ (RealRadius k : Int)) : RealB k :=
  ⟨Int.toNat (z + RealRadius k), by
    have hnonneg : 0 ≤ z + RealRadius k := by omega
    rw [Int.toNat_lt hnonneg]
    omega⟩

theorem candidates_ne_nil (k : ℕ) : candidates k ≠ [] := by
  intro h
  have hmem : (default k) ∈ candidates k := by
    simp [candidates, default]
  simp [h] at hmem

theorem default_mem_candidates (k : ℕ) : default k ∈ candidates k := by
  simp [candidates, default]

@[simp] theorem mem_candidates {k : ℕ} (x : RealB k) : x ∈ candidates k := by
  simp [candidates]

@[simp] theorem toInt_default (k : ℕ) : toInt (default k) = 0 := by
  simp [toInt, default]

@[simp] theorem toRat_default {k : ℕ} (hk : 0 < k) : toRat hk (default k) = 0 := by
  simp [toRat, toInt_default]

@[simp] theorem toInt_ofInt {k : ℕ} (z : Int)
    (hzl : -(RealRadius k : Int) ≤ z) (hzu : z ≤ (RealRadius k : Int)) :
    toInt (ofInt k z hzl hzu) = z := by
  unfold toInt ofInt
  have hnonneg : 0 ≤ z + RealRadius k := by omega
  rw [Int.toNat_of_nonneg hnonneg]
  omega

@[simp] theorem toRat_ofInt {k : ℕ} (hk : 0 < k) (z : Int)
    (hzl : -(RealRadius k : Int) ≤ z) (hzu : z ≤ (RealRadius k : Int)) :
    toRat hk (ofInt k z hzl hzu) = (z : Rat) / ((RealRadius k : ℕ) : Rat) := by
  simp [toRat, toInt_ofInt]

theorem toInt_injective {k : ℕ} : Function.Injective (toInt (k := k)) := by
  intro x y hxy
  apply Fin.ext
  dsimp [toInt] at hxy
  omega

theorem toRat_injective {k : ℕ} (hk : 0 < k) : Function.Injective (toRat hk) := by
  intro x y hxy
  apply toInt_injective
  have hRpos : (0 : Rat) < ((RealRadius k : ℕ) : Rat) := by
    exact_mod_cast (show 0 < RealRadius k by simpa [RealRadius] using pow_pos hk 2)
  have hRne : ((RealRadius k : ℕ) : Rat) ≠ 0 := ne_of_gt hRpos
  have hleft : toRat hk x * ((RealRadius k : ℕ) : Rat) = ((toInt x : Int) : Rat) := by
    unfold toRat
    field_simp [hRne]
  have hright : toRat hk y * ((RealRadius k : ℕ) : Rat) = ((toInt y : Int) : Rat) := by
    unfold toRat
    field_simp [hRne]
  have hcast : ((toInt x : Int) : Rat) = ((toInt y : Int) : Rat) := by
    calc
      ((toInt x : Int) : Rat) = toRat hk x * ((RealRadius k : ℕ) : Rat) := hleft.symm
      _ = toRat hk y * ((RealRadius k : ℕ) : Rat) := by rw [hxy]
      _ = ((toInt y : Int) : Rat) := hright
  exact_mod_cast hcast

theorem argmin_distance_eq_some {k : ℕ} (hk : 0 < k) (q : Rat) :
    ∃ x, (candidates k).argmin (fun x => distance hk x q) = some x := by
  by_cases harg : (candidates k).argmin (fun x => distance hk x q) = none
  · have hnil : candidates k = [] := by
      exact (List.argmin_eq_none (l := candidates k) (f := fun x => distance hk x q)).mp harg
    exact False.elim (candidates_ne_nil k hnil)
  · cases hopt : (candidates k).argmin (fun x => distance hk x q) with
    | none => contradiction
    | some x => exact ⟨x, rfl⟩

theorem round_mem_candidates {k : ℕ} (hk : 0 < k) (q : Rat) :
    round hk q ∈ candidates k := by
  rcases argmin_distance_eq_some hk q with ⟨x, hx⟩
  have hx_mem_argmin : x ∈ (candidates k).argmin (fun y => distance hk y q) := by
    simp [hx]
  have hx_mem_candidates : x ∈ candidates k :=
    List.argmin_mem hx_mem_argmin
  simpa [round, hx] using hx_mem_candidates

set_option maxHeartbeats 400000 in
theorem distance_round_le_distance {k : ℕ} (hk : 0 < k) (q : Rat) {x : RealB k}
    (hx : x ∈ candidates k) :
    distance hk (round hk q) q ≤ distance hk x q := by
  rcases argmin_distance_eq_some hk q with ⟨y, hy⟩
  have hy_mem_argmin : y ∈ (candidates k).argmin (fun z => distance hk z q) := by
    simp [hy]
  have hmin : distance hk y q ≤ distance hk x q :=
    List.le_of_mem_argmin hx hy_mem_argmin
  have hround : round hk q = y := by
    simp [round, hy]
  rw [hround]
  exact hmin

theorem distance_round_le_abs {k : ℕ} (hk : 0 < k) (q : Rat) :
    distance hk (round hk q) q ≤ |q| := by
  simpa [distance, toRat_default] using
    distance_round_le_distance hk q (x := default k) (default_mem_candidates k)

theorem distance_round_self_eq_zero {k : ℕ} (hk : 0 < k) (x : RealB k) :
    distance hk (round hk (toRat hk x)) (toRat hk x) = 0 := by
  have hle : distance hk (round hk (toRat hk x)) (toRat hk x) ≤ distance hk x (toRat hk x) :=
    distance_round_le_distance hk (toRat hk x) (mem_candidates x)
  have hnonneg : 0 ≤ distance hk (round hk (toRat hk x)) (toRat hk x) := by
    unfold distance
    exact abs_nonneg _
  have hle0 : distance hk (round hk (toRat hk x)) (toRat hk x) ≤ 0 := by
    simpa [distance] using hle
  exact le_antisymm hle0 hnonneg

theorem round_self_approxEq_zero {k : ℕ} (hk : 0 < k) (x : RealB k) :
    approxEq hk 0 (round hk (toRat hk x)) x := by
  unfold approxEq
  simpa [distance, abs_sub_comm] using distance_round_self_eq_zero hk x

theorem round_eq_self {k : ℕ} (hk : 0 < k) (x : RealB k) :
    round hk (toRat hk x) = x := by
  apply toRat_injective hk
  have hzero : distance hk (round hk (toRat hk x)) (toRat hk x) = 0 :=
    distance_round_self_eq_zero hk x
  have hrat : |toRat hk (round hk (toRat hk x)) - toRat hk x| = 0 := by
    simpa [distance] using hzero
  exact sub_eq_zero.mp (abs_eq_zero.mp hrat)

@[simp] theorem round_zero_eq_default {k : ℕ} (hk : 0 < k) :
    round hk 0 = default k := by
  simpa [toRat_default] using round_eq_self hk (default k)

@[simp] theorem add_default_right {k : ℕ} (hk : 0 < k) (x : RealB k) :
    add hk x (default k) = x := by
  unfold add
  simpa [toRat_default, add_comm] using round_eq_self hk x

@[simp] theorem add_default_left {k : ℕ} (hk : 0 < k) (x : RealB k) :
    add hk (default k) x = x := by
  unfold add
  simpa [toRat_default] using round_eq_self hk x

@[simp] theorem sub_self {k : ℕ} (hk : 0 < k) (x : RealB k) :
    sub hk x x = default k := by
  unfold sub
  simp

@[simp] theorem sub_default_right {k : ℕ} (hk : 0 < k) (x : RealB k) :
    sub hk x (default k) = x := by
  unfold sub
  simpa [toRat_default] using round_eq_self hk x

@[simp] theorem mul_default_right {k : ℕ} (hk : 0 < k) (x : RealB k) :
    mul hk x (default k) = default k := by
  unfold mul
  simp [toRat_default]

@[simp] theorem mul_default_left {k : ℕ} (hk : 0 < k) (x : RealB k) :
    mul hk (default k) x = default k := by
  unfold mul
  simp [toRat_default]

theorem halfStep_nonneg (k : ℕ) : 0 ≤ halfStep k := by
  unfold halfStep
  positivity

theorem approxEq_refl {k : ℕ} (hk : 0 < k) (ε : Rat) (hε : 0 ≤ ε) (x : RealB k) :
    approxEq hk ε x x := by
  unfold approxEq
  simpa using hε

theorem approxEq_symm {k : ℕ} (hk : 0 < k) (ε : Rat) (x y : RealB k) :
    approxEq hk ε x y ↔ approxEq hk ε y x := by
  unfold approxEq
  constructor <;> intro h <;> simpa [abs_sub_comm] using h

theorem approxEq_triangle {k : ℕ} (hk : 0 < k) (ε₁ ε₂ : Rat) (x y z : RealB k)
    (hxy : approxEq hk ε₁ x y) (hyz : approxEq hk ε₂ y z) :
    approxEq hk (ε₁ + ε₂) x z := by
  unfold approxEq at hxy hyz ⊢
  have hsplit :
      toRat hk x - toRat hk z =
        (toRat hk x - toRat hk y) + (toRat hk y - toRat hk z) := by
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans <| by linarith

theorem distance_round_le_halfStep_of_abs_le_one {k : ℕ} (hk : 0 < k) {q : Rat}
    (hq : |q| ≤ 1) :
    distance hk (round hk q) q ≤ halfStep k := by
  let R : Rat := ((RealRadius k : ℕ) : Rat)
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < RealRadius k by simpa [RealRadius] using pow_pos hk 2)
  have hq_bounds : (-1 : Rat) ≤ q ∧ q ≤ 1 := abs_le.mp hq
  let t : Rat := q * R + (1 / 2 : Rat)
  let n : Int := ⌊t⌋
  have hn_lower : -(RealRadius k : Int) ≤ n := by
    apply Int.le_floor.mpr
    change (-R : Rat) ≤ t
    dsimp [t]
    nlinarith [hq_bounds.1, hRpos]
  have hn_upper : n ≤ (RealRadius k : Int) := by
    rw [Int.floor_le_iff]
    change t < R + 1
    dsimp [t]
    nlinarith [hq_bounds.2, hRpos]
  let x : RealB k := ofInt k n hn_lower hn_upper
  have hx_min : distance hk (round hk q) q ≤ distance hk x q :=
    distance_round_le_distance hk q (mem_candidates x)
  have hx_rat : toRat hk x = (n : Rat) / R := by
    simpa [R, x] using toRat_ofInt hk n hn_lower hn_upper
  have hnum_repr : ((n : Rat) - q * R) = (1 / 2 : Rat) - Int.fract t := by
    dsimp [t, n]
    rw [Int.fract]
    ring
  have hnum_abs : |(n : Rat) - q * R| ≤ (1 / 2 : Rat) := by
    rw [hnum_repr]
    apply abs_le.mpr
    constructor <;> nlinarith [Int.fract_nonneg t, Int.fract_lt_one t]
  have hx_bound : distance hk x q ≤ halfStep k := by
    unfold distance halfStep
    rw [hx_rat]
    have hRne : R ≠ 0 := ne_of_gt hRpos
    have hsub : (n : Rat) / R - q = ((n : Rat) - q * R) / R := by
      field_simp [hRne]
    rw [hsub, abs_div, abs_of_pos hRpos]
    exact div_le_div_of_nonneg_right hnum_abs hRpos.le
  exact le_trans hx_min hx_bound

theorem mul_error_le_halfStep_of_abs_le_one {k : ℕ} (hk : 0 < k) (x y : RealB k)
    (hxy : |toRat hk x * toRat hk y| ≤ 1) :
    |toRat hk (mul hk x y) - (toRat hk x * toRat hk y)| ≤ halfStep k := by
  unfold mul
  simpa [distance] using distance_round_le_halfStep_of_abs_le_one hk hxy

theorem add_error_le_halfStep_of_abs_le_one {k : ℕ} (hk : 0 < k) (x y : RealB k)
    (hxy : |toRat hk x + toRat hk y| ≤ 1) :
    |toRat hk (add hk x y) - (toRat hk x + toRat hk y)| ≤ halfStep k := by
  unfold add
  simpa [distance] using distance_round_le_halfStep_of_abs_le_one hk hxy

end RealB

end HeytingLean.BST
