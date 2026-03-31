import HeytingLean.Eigen.ParametricHeyting

namespace HeytingLean
namespace Eigen

/-!
# Learnable Heyting Bounds Properties

Properties backing Python `LearnableBounds` for PINN export certification.
These theorems ensure that the clamp and Heyting operations maintain bounds
and have the expected monotonicity properties.

All theorems operate on `PBVec n lo hi`, the bounded vector type from
`ParametricHeyting`, with operations:
- `clamp`: project arbitrary vectors into bounds
- `meet`/`join`: componentwise min/max
- `himp`: bounded Heyting implication
- `hnot`: pseudocomplement
-/

open scoped Classical

noncomputable section

variable {n : Nat} {lo hi : Fin n → ℝ}

namespace PBVec

/-! ## Clamp Properties -/

/-- The clamped output is always within bounds. (Trivial by definition) -/
theorem clamp_mem_bounds (x : Fin n → ℝ) (hlohi : ∀ i, lo i ≤ hi i) :
    let v := clamp (lo := lo) (hi := hi) x hlohi
    (∀ i, lo i ≤ v i) ∧ (∀ i, v i ≤ hi i) :=
  (clamp x hlohi).property

/-- Clamping is idempotent: clamp (clamp v) = clamp v. -/
theorem clamp_idempotent (x : Fin n → ℝ) (hlohi : ∀ i, lo i ≤ hi i) :
    clamp (lo := lo) (hi := hi) (clamp x hlohi).val hlohi = clamp x hlohi := by
  ext i
  simp only [clamp, Subtype.coe_mk]
  -- Goal: max (lo i) (min (max (lo i) (min (x i) (hi i))) (hi i)) = max (lo i) (min (x i) (hi i))
  set c := max (lo i) (min (x i) (hi i)) with hc
  -- Show: max (lo i) (min c (hi i)) = c
  have hlo_c : lo i ≤ c := le_max_left _ _
  have hc_hi : c ≤ hi i := max_le (hlohi i) (min_le_right _ _)
  rw [min_eq_left hc_hi, max_eq_right hlo_c]

/-- Clamping is monotone: x ≤ y → clamp x ≤ clamp y. -/
theorem clamp_monotone (x y : Fin n → ℝ) (hlohi : ∀ i, lo i ≤ hi i)
    (hxy : ∀ i, x i ≤ y i) :
    ∀ i, (clamp (lo := lo) (hi := hi) x hlohi).val i ≤
         (clamp (lo := lo) (hi := hi) y hlohi).val i := by
  intro i
  simp only [clamp, Subtype.coe_mk]
  apply max_le_max_left
  apply min_le_min_right
  exact hxy i

/-! ## Meet/Join Preserve Bounds -/

/-- Meet preserves bounds. (Trivial by construction) -/
theorem meet_bounds (a b : PBVec n lo hi) :
    let v := meet a b
    (∀ i, lo i ≤ v i) ∧ (∀ i, v i ≤ hi i) :=
  (meet a b).property

/-- Join preserves bounds. (Trivial by construction) -/
theorem join_bounds (a b : PBVec n lo hi) :
    let v := join a b
    (∀ i, lo i ≤ v i) ∧ (∀ i, v i ≤ hi i) :=
  (join a b).property

/-! ## Heyting Operations Preserve Bounds -/

/-- Heyting implication preserves bounds. (Trivial by construction) -/
theorem himp_bounds (a b : PBVec n lo hi) (hlohi : ∀ i, lo i ≤ hi i) :
    let v := himp a b hlohi
    (∀ i, lo i ≤ v i) ∧ (∀ i, v i ≤ hi i) :=
  (himp a b hlohi).property

/-- Heyting negation preserves bounds. (Trivial by construction) -/
theorem hnot_bounds (a : PBVec n lo hi) (hlohi : ∀ i, lo i ≤ hi i) :
    let v := hnot a hlohi
    (∀ i, lo i ≤ v i) ∧ (∀ i, v i ≤ hi i) :=
  (hnot a hlohi).property

/-! ## Monotonicity of Heyting Operations -/

/-- Meet is monotone in both arguments. -/
theorem meet_monotone (a₁ a₂ b₁ b₂ : PBVec n lo hi)
    (ha : ∀ i, a₁ i ≤ a₂ i) (hb : ∀ i, b₁ i ≤ b₂ i) :
    ∀ i, (meet a₁ b₁) i ≤ (meet a₂ b₂) i := by
  intro i
  simp only [meet, Subtype.coe_mk]
  exact min_le_min (ha i) (hb i)

/-- Join is monotone in both arguments. -/
theorem join_monotone (a₁ a₂ b₁ b₂ : PBVec n lo hi)
    (ha : ∀ i, a₁ i ≤ a₂ i) (hb : ∀ i, b₁ i ≤ b₂ i) :
    ∀ i, (join a₁ b₁) i ≤ (join a₂ b₂) i := by
  intro i
  simp only [join, Subtype.coe_mk]
  exact max_le_max (ha i) (hb i)

/-- Heyting implication is monotone in the second argument.
    If b₁ ≤ b₂ then (a ↣ b₁) ≤ (a ↣ b₂). -/
theorem himp_monotone_right (a b₁ b₂ : PBVec n lo hi) (hlohi : ∀ i, lo i ≤ hi i)
    (hb : ∀ i, b₁ i ≤ b₂ i) :
    ∀ i, (himp a b₁ hlohi) i ≤ (himp a b₂ hlohi) i := by
  intro i
  simp only [himp, Subtype.coe_mk]
  by_cases h1 : a i ≤ b₁ i
  · -- a ≤ b₁ ≤ b₂, so both are hi
    have h2 : a i ≤ b₂ i := le_trans h1 (hb i)
    simp [h1, h2]
  · -- a > b₁
    by_cases h2 : a i ≤ b₂ i
    · -- a ≤ b₂ but a > b₁, so result is b₁ i ≤ hi i
      simp [h1, h2, le_hi b₁ i]
    · -- a > b₂ as well, so both results are b_i
      simp [h1, h2, hb i]

/-- Heyting implication is antitone in the first argument.
    If a₁ ≤ a₂ then (a₂ ↣ b) ≤ (a₁ ↣ b). -/
theorem himp_antitone_left (a₁ a₂ b : PBVec n lo hi) (hlohi : ∀ i, lo i ≤ hi i)
    (ha : ∀ i, a₁ i ≤ a₂ i) :
    ∀ i, (himp a₂ b hlohi) i ≤ (himp a₁ b hlohi) i := by
  intro i
  simp only [himp, Subtype.coe_mk]
  by_cases h2 : a₂ i ≤ b i
  · -- a₂ ≤ b, so a₁ ≤ b too, both results are hi
    have h1 : a₁ i ≤ b i := le_trans (ha i) h2
    simp [h1, h2]
  · -- a₂ > b
    by_cases h1 : a₁ i ≤ b i
    · -- a₁ ≤ b < a₂, result is b i ≤ hi i
      simp [h1, h2, le_hi b i]
    · -- a₁ > b too, both results are b i
      simp [h1, h2]

/-! ## Additional Properties for Export Certification -/

/-- Helper: characterize clamp value based on position relative to bounds. -/
private theorem clamp_val_eq (x : Fin n → ℝ) (hlohi : ∀ i, lo i ≤ hi i) (i : Fin n) :
    (clamp (lo := lo) (hi := hi) x hlohi).val i =
      if x i ≤ lo i then lo i
      else if hi i ≤ x i then hi i
      else x i := by
  simp only [clamp, Subtype.coe_mk]
  split_ifs with hxlo hxhi
  · -- x ≤ lo
    rw [min_eq_left (le_trans hxlo (hlohi i)), max_eq_left hxlo]
  · -- lo < x and hi ≤ x
    rw [min_eq_right hxhi, max_eq_right (hlohi i)]
  · -- lo < x < hi
    push_neg at hxlo hxhi
    rw [min_eq_left (le_of_lt hxhi), max_eq_right (le_of_lt hxlo)]

/-- Clamp distributes over meet (after clamping inputs). -/
theorem clamp_meet_distrib (x y : Fin n → ℝ) (hlohi : ∀ i, lo i ≤ hi i) :
    meet (clamp (lo := lo) (hi := hi) x hlohi) (clamp y hlohi) =
    clamp (fun i => min (x i) (y i)) hlohi := by
  ext i
  simp only [meet, Subtype.coe_mk]
  rw [clamp_val_eq x hlohi i, clamp_val_eq y hlohi i, clamp_val_eq (fun j => min (x j) (y j)) hlohi i]
  -- Case analysis on x and y positions relative to [lo, hi]
  by_cases hxlo : x i ≤ lo i
  · -- Case: x ≤ lo
    rw [if_pos hxlo]
    have hmlo : min (x i) (y i) ≤ lo i := min_le_of_left_le hxlo
    rw [if_pos hmlo]
    by_cases hylo : y i ≤ lo i
    · rw [if_pos hylo, min_self]
    · rw [if_neg hylo]
      by_cases hyhi : hi i ≤ y i
      · rw [if_pos hyhi, min_eq_left (hlohi i)]
      · rw [if_neg hyhi, min_eq_left (le_of_not_ge hylo)]
  · -- Case: lo < x
    rw [if_neg hxlo]
    by_cases hxhi : hi i ≤ x i
    · -- Case: x ≥ hi
      rw [if_pos hxhi]
      by_cases hylo : y i ≤ lo i
      · rw [if_pos hylo]
        have hmlo : min (x i) (y i) ≤ lo i := min_le_of_right_le hylo
        rw [if_pos hmlo, min_eq_right (hlohi i)]
      · rw [if_neg hylo]
        by_cases hyhi : hi i ≤ y i
        · rw [if_pos hyhi, min_self]
          have hmhi : hi i ≤ min (x i) (y i) := le_min hxhi hyhi
          have hmlo' : ¬(min (x i) (y i) ≤ lo i) :=
            not_le.mpr (lt_min (not_le.mp hxlo) (not_le.mp hylo))
          rw [if_neg hmlo', if_pos hmhi]
        · rw [if_neg hyhi]
          -- x ≥ hi, lo < y < hi, so min(x,y) = y
          have hxy : y i ≤ x i := le_trans (le_of_lt (not_le.mp hyhi)) hxhi
          rw [min_eq_right hxy]
          have hmlo' : ¬(y i ≤ lo i) := hylo
          have hmhi' : ¬(hi i ≤ y i) := hyhi
          rw [if_neg hmlo', if_neg hmhi']
          exact min_eq_right (le_of_lt (not_le.mp hyhi))
    · -- Case: lo < x < hi
      rw [if_neg hxhi]
      by_cases hylo : y i ≤ lo i
      · rw [if_pos hylo]
        have hmlo : min (x i) (y i) ≤ lo i := min_le_of_right_le hylo
        rw [if_pos hmlo, min_eq_right (le_of_not_ge hxlo)]
      · rw [if_neg hylo]
        by_cases hyhi : hi i ≤ y i
        · rw [if_pos hyhi]
          -- lo < x < hi, y ≥ hi, so min(x,y) = x
          have hxy : x i ≤ y i := le_trans (le_of_lt (not_le.mp hxhi)) hyhi
          rw [min_eq_left hxy]
          have hmlo' : ¬(x i ≤ lo i) := hxlo
          have hmhi' : ¬(hi i ≤ x i) := hxhi
          rw [if_neg hmlo', if_neg hmhi']
          exact min_eq_left (le_of_lt (not_le.mp hxhi))
        · rw [if_neg hyhi]
          -- lo < x < hi and lo < y < hi, so min stays in range
          have hmlo' : ¬(min (x i) (y i) ≤ lo i) :=
            not_le.mpr (lt_min (not_le.mp hxlo) (not_le.mp hylo))
          have hmhi' : ¬(hi i ≤ min (x i) (y i)) :=
            not_le.mpr (lt_of_le_of_lt (min_le_left _ _) (not_le.mp hxhi))
          rw [if_neg hmlo', if_neg hmhi']

/-- Clamp of a bounded vector is identity. -/
theorem clamp_of_bounded (v : PBVec n lo hi) (hlohi : ∀ i, lo i ≤ hi i) :
    clamp (lo := lo) (hi := hi) v.val hlohi = v := by
  ext i
  simp only [clamp, Subtype.coe_mk]
  rw [min_eq_left (le_hi v i), max_eq_right (ge_lo v i)]

end PBVec

end
end Eigen
end HeytingLean
