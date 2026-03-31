import Mathlib.Data.Real.Basic
import Mathlib.Order.MinMax

namespace HeytingLean
namespace Eigen

open scoped Classical

noncomputable section

/-!
Bounded Heyting-style operations on a bounded nonnegative orthant.

For the ReLU nucleus on `Fin n → ℝ`, the fixed points are `∀ i, 0 ≤ v i`,
which is not a bounded lattice (no global ⊤). For “logic-like” operations we
therefore work in a bounded orthant `[0, top]^n`.

We define:
- meet: componentwise `min`
- join: componentwise `max`
- implication (bounded): `(a ↣ b)_i := if a_i ≤ b_i then top else b_i`
- negation: `¬a := a ↣ ⊥`

and prove the defining adjunction law:

  (a ⊓ c ≤ b) ↔ (c ≤ a ↣ b).
-/

variable {n : Nat} {top : ℝ}

/-- Bounded nonnegative vectors `[0, top]^n` as a subtype of `Fin n → ℝ`. -/
abbrev BVec (n : Nat) (top : ℝ) := { v : Fin n → ℝ // (∀ i, 0 ≤ v i) ∧ (∀ i, v i ≤ top) }

namespace BVec

instance : CoeFun (BVec n top) (fun _ => Fin n → ℝ) where
  coe v := v.val

@[simp] theorem coe_mk (v : Fin n → ℝ) (hv) : ((⟨v, hv⟩ : BVec n top) : Fin n → ℝ) = v := rfl

theorem nonneg (v : BVec n top) : ∀ i, 0 ≤ (v : Fin n → ℝ) i := v.property.1
theorem le_top (v : BVec n top) : ∀ i, (v : Fin n → ℝ) i ≤ top := v.property.2

@[ext] theorem ext {a b : BVec n top} (h : ∀ i, a i = b i) : a = b := by
  apply Subtype.ext
  funext i
  exact h i

/-- Componentwise meet (inf): `min`. -/
def meet (a b : BVec n top) : BVec n top :=
  ⟨fun i => min (a i) (b i),
    ⟨fun i => le_min (nonneg a i) (nonneg b i),
     fun i => le_trans (min_le_left _ _) (le_top a i)⟩⟩

/-- Componentwise join (sup): `max`. -/
def join (a b : BVec n top) : BVec n top :=
  ⟨fun i => max (a i) (b i),
    ⟨fun i =>
        le_trans (nonneg a i) (le_max_left _ _),
     fun i =>
        max_le (le_top a i) (le_top b i)⟩⟩

/-- Bottom element: the zero vector. -/
def bot (n : Nat) (top : ℝ) (htop : 0 ≤ top) : BVec n top :=
  ⟨fun _ => 0, ⟨fun _ => le_rfl, fun _ => htop⟩⟩

/-- Top element: the constant `top` vector (requires `0 ≤ top`). -/
def topElem (n : Nat) (top : ℝ) (htop : 0 ≤ top) : BVec n top :=
  ⟨fun _ => top, ⟨fun _ => htop, fun _ => le_rfl⟩⟩

/-- Bounded Heyting-style implication (requires `0 ≤ top`). -/
def himp (a b : BVec n top) (htop : 0 ≤ top) : BVec n top :=
  ⟨fun i => if a i ≤ b i then top else b i,
    ⟨fun i => by
        by_cases h : a i ≤ b i
        · simp [h, htop]
        · simp [h, nonneg b i],
     fun i => by
        by_cases h : a i ≤ b i
        · simp [h]
        · simp [h, le_top b i]⟩⟩

/-- Negation / pseudocomplement: `¬a := a ↣ ⊥`. -/
def hnot (a : BVec n top) (htop : 0 ≤ top) : BVec n top :=
  himp a (bot n top htop) htop

theorem meet_comm (a b : BVec n top) : meet a b = meet b a := by
  ext i
  simp [meet, min_comm]

theorem meet_assoc (a b c : BVec n top) : meet (meet a b) c = meet a (meet b c) := by
  ext i
  simp [meet, min_assoc]

theorem meet_idem (a : BVec n top) : meet a a = a := by
  ext i
  simp [meet, min_self]

theorem join_comm (a b : BVec n top) : join a b = join b a := by
  ext i
  simp [join, max_comm]

theorem join_assoc (a b c : BVec n top) : join (join a b) c = join a (join b c) := by
  ext i
  simp [join, max_assoc]

theorem meet_join_absorb (a b : BVec n top) : meet a (join a b) = a := by
  ext i
  -- `min a (max a b) = a`.
  simp [meet, join]

theorem join_meet_absorb (a b : BVec n top) : join a (meet a b) = a := by
  ext i
  -- `max a (min a b) = a`.
  simp [meet, join]

/--
Adjunction law (defining Heyting implication):

`a ⊓ c ≤ b` iff `c ≤ a ↣ b`.
-/
theorem himp_adjoint (a b c : BVec n top) (htop : 0 ≤ top) :
    meet a c ≤ b ↔ c ≤ himp a b htop := by
  constructor
  · intro h i
    have hmin : min (a i) (c i) ≤ b i := h i
    by_cases hab : a i ≤ b i
    · -- implication is `top`, and `c i ≤ top` by boundedness
      simpa [himp, hab] using (le_top c i)
    · -- implication is `b i`, so show `c i ≤ b i` (else we contradict `hab`)
      have hab' : b i < a i := lt_of_not_ge hab
      by_cases hac : a i ≤ c i
      · have : a i ≤ b i := by simpa [min_eq_left hac] using hmin
        exact False.elim (hab this)
      · have hac' : c i < a i := lt_of_not_ge hac
        have : c i ≤ b i := by
          simpa [min_eq_right (le_of_lt hac')] using hmin
        simpa [himp, hab] using this
  · intro h i
    by_cases hab : a i ≤ b i
    · have : a i ≤ b i := hab
      exact le_trans (min_le_left _ _) this
    · have hc : c i ≤ b i := by
        have := h i
        simpa [himp, hab] using this
      exact le_trans (min_le_right _ _) hc

theorem boundary_eq_bot (a : BVec n top) (htop : 0 ≤ top) :
    meet a (hnot a htop) = bot n top htop := by
  ext i
  by_cases ha0 : a i = 0
  · -- then `(hnot a) i = top` and `min 0 top = 0`
    have hle : a i ≤ (0 : ℝ) := by simp [ha0]
    have hnot_i : (hnot a htop) i = top := by
      simp [hnot, himp, bot, hle]
    -- `min 0 top = 0` since `0 ≤ top`.
    have : min (0 : ℝ) top = 0 := min_eq_left htop
    simp [meet, bot, ha0, hnot_i, this]
  · -- then `0 < a i` and `(hnot a) i = 0`, so `min a_i 0 = 0`
    have ha_pos : 0 < a i := lt_of_le_of_ne (nonneg a i) (Ne.symm ha0)
    have hle : ¬a i ≤ (0 : ℝ) := not_le_of_gt ha_pos
    have hnot_i : (hnot a htop) i = 0 := by
      simp [hnot, himp, bot, hle]
    have : min (a i) (0 : ℝ) = 0 := min_eq_right (nonneg a i)
    simp [meet, bot, hnot_i, this]

theorem double_neg_coord (a : BVec n top) (htop : 0 ≤ top) (i : Fin n) :
    (hnot (hnot a htop) htop) i = (if a i = 0 then 0 else top) := by
  by_cases ha0 : a i = 0
  · have hle : a i ≤ (0 : ℝ) := by simp [ha0]
    have hnot_i : (hnot a htop) i = top := by
      simp [hnot, himp, bot, hle]
    have : (hnot (hnot a htop) htop) i = 0 := by
      change (himp (hnot a htop) (bot n top htop) htop) i = 0
      by_cases ht0 : top = 0
      · subst ht0
        simp [himp, bot]
      · have htop0 : ¬top ≤ (0 : ℝ) := by
          have : 0 < top := lt_of_le_of_ne htop (Ne.symm ht0)
          exact not_le_of_gt this
        simp [himp, bot, hnot_i, htop0]
    simp [ha0, this]
  · have ha_pos : 0 < a i := lt_of_le_of_ne (nonneg a i) (Ne.symm ha0)
    have hle : ¬a i ≤ (0 : ℝ) := not_le_of_gt ha_pos
    have hnot_i : (hnot a htop) i = 0 := by
      simp [hnot, himp, bot, hle]
    -- Now `0 ≤ 0`, so second negation returns `top`.
    have : (hnot (hnot a htop) htop) i = top := by
      change (himp (hnot a htop) (bot n top htop) htop) i = top
      have hcond : (hnot a htop) i ≤ (0 : ℝ) := by simp [hnot_i]
      simp [himp, bot, hnot_i]
    simp [ha0, this]

theorem not_not_ne (a : BVec n top) (htop : 0 < top)
    (ha : ∃ i, 0 < a i ∧ a i < top) :
    hnot (hnot a (le_of_lt htop)) (le_of_lt htop) ≠ a := by
  intro h
  obtain ⟨i, hi_pos, hi_lt⟩ := ha
  have hcoord :
      (hnot (hnot a (le_of_lt htop)) (le_of_lt htop)) i = a i := by
    simpa using congrArg (fun v => v i) h
  have ha0 : a i ≠ 0 := ne_of_gt hi_pos
  have : (hnot (hnot a (le_of_lt htop)) (le_of_lt htop)) i = top := by
    simp [double_neg_coord, ha0]
  have : top = a i := by simpa [this] using hcoord
  exact (ne_of_lt hi_lt) this.symm

end BVec

end

end Eigen
end HeytingLean
