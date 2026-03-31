import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerDeep.Requirements
import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerDeep.Basic
import Mathlib

/- This file contains proof for the Kochen-Specker paradox. See Basic.lean for data definitions and helper lemmas -/

namespace HeytingLean
namespace Noneism
namespace Contextuality
namespace KochenSpeckerDeep

open SpinMeasurement
open scoped Matrix

/-- Tactics for simplifying vector normalization and orthogonality proofs -/

syntax "vec_norm" : tactic
macro_rules
  | `(tactic| vec_norm) => `(tactic| first
    | (simp ;ring_nf ; simp ; norm_num)
    | (simp ; ring_nf ; simp)
    | simp)

syntax "prove_orth" : tactic
macro_rules
  | `(tactic| prove_orth) => `(tactic|
      (apply (Iff.mpr (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ))
       ext i j
       fin_cases i <;> fin_cases j
       all_goals
         (simp [Matrix.mul_apply, Fin.sum_univ_three] ; try ring_nf)))

private lemma sqrt_two_sq : (Real.sqrt 2)^2 = (2 : ℝ) := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma sqrt_three_sq : (Real.sqrt 3)^2 = (3 : ℝ) := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- Measurement directions for Kochen-Specker construction. Naming based on the position/role in the proof -/

noncomputable def x : MeasurementDirection := ⟨![1, 0, 0], by vec_norm⟩
noncomputable def y : MeasurementDirection := ⟨![0, 1, 0], by vec_norm⟩
noncomputable def z : MeasurementDirection := ⟨![0, 0, 1], by vec_norm⟩

noncomputable def a1 : MeasurementDirection := ⟨![0, 1 / √2, 1 / √2], by vec_norm⟩
noncomputable def a2 : MeasurementDirection := ⟨![0, -1 / √2, 1 / √2], by vec_norm⟩
noncomputable def a3 : MeasurementDirection := ⟨![0, -1 / √2, -1 / √2], by vec_norm⟩

noncomputable def b1 : MeasurementDirection := ⟨![1 / √2, 1 / 2, 1 / 2], by vec_norm⟩
noncomputable def b2 : MeasurementDirection := ⟨![1 / √2, -1 / 2, -1 / 2], by vec_norm⟩
noncomputable def b3 : MeasurementDirection := ⟨![1 / √2, -1 / 2, 1 / 2], by vec_norm⟩
noncomputable def b4 : MeasurementDirection := ⟨![1 / √2, 1 / 2, -1 / 2], by vec_norm⟩

noncomputable def c1 : MeasurementDirection := ⟨![-1 / √3, √2 / √3, 0], by vec_norm⟩
noncomputable def c2 : MeasurementDirection := ⟨![1 / √3, √2 / √3, 0], by vec_norm⟩
noncomputable def d1 : MeasurementDirection := ⟨![√2 / √3, 1 / √3, 0], by vec_norm⟩
noncomputable def d2 : MeasurementDirection := ⟨![√2 / √3, -1 / √3, 0], by vec_norm⟩

noncomputable def e1 : MeasurementDirection := ⟨![-1 / 2, 1 / √2, 1 / 2], by vec_norm⟩
noncomputable def e2 : MeasurementDirection := ⟨![-1 / 2, 1 / √2, -1 / 2], by vec_norm⟩
noncomputable def e3 : MeasurementDirection := ⟨![1 / 2, 1 / √2, 1 / 2], by vec_norm⟩
noncomputable def e4 : MeasurementDirection := ⟨![1 / 2, 1 / √2, -1 / 2], by vec_norm⟩

noncomputable def f1 : MeasurementDirection := ⟨![-1 / √2, 0, 1 / √2], by vec_norm⟩
noncomputable def f2 : MeasurementDirection := ⟨![1 / √2, 0, 1 / √2], by vec_norm⟩

/-- Perpendicularity proofs for measurement directions -/

theorem perp_xyz : IsMutuallyPerpendicular x y z :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [x, y])
  apply And.intro (by simp [y, z]) (by simp [x, z])

theorem perp_a2b1b2 : IsMutuallyPerpendicular a2 b1 b2 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [a2, b1] ; ring_nf)
  apply And.intro (by simp [b1, b2] ; ring_nf ; norm_num) (by simp [a2, b2] ; ring_nf)

theorem perp_a1b3b4 : IsMutuallyPerpendicular a1 b3 b4 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [a1, b3] ; ring_nf)
  apply And.intro (by simp [b3, b4] ; ring_nf ; norm_num) (by simp [a1, b4] ; ring_nf)

theorem perp_c1zd1 : IsMutuallyPerpendicular c1 z d1 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [c1, z])
  apply And.intro (by simp [z,d1]) (by simp [c1, d1] ; ring_nf)

theorem perp_c2zd2 : IsMutuallyPerpendicular c2 z d2 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by simp [c2, z])
  apply And.intro (by simp [z, d2]) (by simp [c2, d2] ; ring_nf)

theorem perp_e2e3f1 : IsMutuallyPerpendicular e2 e3 f1 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by
    simp [e2, e3]
    field_simp
    rw [sqrt_two_sq]
    ring_nf)
  apply And.intro (by simp [e3, f1] ; ring_nf) (by simp [e2, f1] ; ring_nf)

theorem perp_e1e4f2 : IsMutuallyPerpendicular e1 e4 f2 :=
by
  rw [IsMutuallyPerpendicular] ; repeat rw [IsPerpendicular]
  apply And.intro (by
    simp [e1, e4]
    field_simp
    rw [sqrt_two_sq]
    ring_nf)
  apply And.intro (by simp [e4, f2] ; ring_nf) (by simp [e1, f2] ; ring_nf)

theorem perp_xa1 : IsPerpendicular x a1 :=
by
  rw [IsPerpendicular]
  simp [x, a1]

theorem perp_xa2 : IsPerpendicular x a2 :=
by
  rw [IsPerpendicular]
  simp [x, a2]

theorem perp_xa3 : IsPerpendicular x a3 :=
by
  rw [IsPerpendicular]
  simp [x, a3]

theorem perp_b1c1 : IsPerpendicular b1 c1 :=
by
  rw [IsPerpendicular]
  simp [b1, c1] ; norm_num ; field_simp ; ring_nf ; norm_num

theorem perp_b3c2 : IsPerpendicular b3 c2 :=
by
  rw [IsPerpendicular]
  simp [b3, c2] ; norm_num ; field_simp ; ring_nf ; norm_num

theorem perp_xz : IsPerpendicular x z :=
by
  rw [IsPerpendicular]
  simp [x, z]

theorem perp_f1f2 : IsPerpendicular f1 f2 :=
by
  rw [IsPerpendicular]
  simp [f1, f2] ; field_simp ; ring_nf

theorem perp_d1e1 : IsPerpendicular d1 e1 :=
by
  rw [IsPerpendicular]
  simp [d1, e1]
  field_simp
  rw [sqrt_two_sq]
  ring_nf

theorem perp_d2e3 : IsPerpendicular d2 e3 :=
by
  rw [IsPerpendicular]
  simp [d2, e3]
  field_simp
  rw [sqrt_two_sq]
  ring_nf

theorem perp_d1e2 : IsPerpendicular d1 e2 :=
by
  rw [IsPerpendicular]
  simp [d1, e2]
  field_simp
  rw [sqrt_two_sq]
  ring_nf

theorem perp_d2e4 : IsPerpendicular d2 e4 :=
by
  rw [IsPerpendicular]
  simp [d2, e4]
  field_simp
  rw [sqrt_two_sq]
  ring_nf

/-- O3 group rotations. To be used for WLOG arguments -/

def rotxyz_yxz : O3 :=
  {
    matrix := !![0, 1, 0 ; 1, 0, 0; 0, 0, 1],
    is_orth :=  by prove_orth
  }

def rotxyz_zyx : O3 :=
  {
    matrix := !![0, 0, 1 ; 0, 1, 0; 1, 0, 0],
    is_orth :=  by prove_orth
  }

def rotxyz_xzy : O3 :=
  {
    matrix := !![1, 0, 0 ; 0, 0, 1; 0, 1, 0],
    is_orth :=  by prove_orth
  }

def rotxyz_xnzny : O3 :=
  {
    matrix := !![1, 0, 0 ; 0, 0, -1; 0, -1, 0],
    is_orth :=  by prove_orth
  }

/-- Main Kochen-Specker theorem steps -/

/- Step 1: Existence of a `OneZeroOneFunc` implies existence of a `OneZeroOneFunc` that assigns `zero` to `x` -/

theorem kochen_specker_step_1 (f : OneZeroOneFunc):
  ∃ f : OneZeroOneFunc,  apply f x = zero :=
by
  have hin : [apply f x, apply f y, apply f z] ∈ ValidThriples := f.property x y z perp_xyz
  rw [ValidThriples] at hin ; simp at hin
  cases hin with
  | inl heq => exact Exists.intro f heq.left
  | inr heq => cases heq with
    | inl heq =>
      apply Exists.intro (rotxyz_yxz.compose_OneZeroOneFunc f)
      rw [O3.compose_OneZeroOneFunc, apply] ; simp
      have hrotn : rotxyz_yxz.function x = y := by
        rw [O3.function, x, y] ; simp [rotxyz_yxz]; apply Subtype.eq ; exact Iff.mp List.ofFn_inj rfl
      rw [hrotn]
      exact heq.right.left
    | inr heq =>
      apply Exists.intro (rotxyz_zyx.compose_OneZeroOneFunc f)
      rw [O3.compose_OneZeroOneFunc, apply] ; simp
      have hrotn : rotxyz_zyx.function x = z := by
        rw [O3.function, x, z] ; simp [rotxyz_zyx]; apply Subtype.eq ; exact Iff.mp List.ofFn_inj rfl
      rw [hrotn]
      exact heq.right.right

/- Step 2: Result of `kochen_specker_step_1` implies existence of a `OneZeroOneFunc` that assigns `zero` to `x` and `b1` -/

theorem kochen_specker_step_2 (f : OneZeroOneFunc) (hx : apply f x = zero) :
  ∃ f : OneZeroOneFunc, apply f x = zero ∧ apply f b1 = zero :=
by
  have ha2 : apply f a2 = one := by
    apply perp_zero_implies_one f x a2 hx perp_xa2
  have hin : [apply f a2, apply f b1, apply f b2] ∈ ValidThriples := f.property a2 b1 b2 perp_a2b1b2
  rw [ValidThriples] at hin ; simp at hin
  cases hin with
  | inl heq =>
    rw [heq.left] at ha2
    contradiction
  | inr heq => cases heq with
    | inl heq =>
      exact Exists.intro f (And.intro hx heq.right.left)
    | inr heq =>
      apply Exists.intro (rotxyz_xnzny.compose_OneZeroOneFunc f)
      repeat rw [O3.compose_OneZeroOneFunc] ; repeat rw [apply] ; simp
      have hrotxx : rotxyz_xnzny.function x = x := by
        simp [O3.function, x, rotxyz_xnzny]
        apply Subtype.eq ; exact Iff.mp List.ofFn_inj rfl
      have hrotb1b2 : rotxyz_xnzny.function b1 = b2 := by
        simp [O3.function, b1, b2, rotxyz_xnzny]
        apply Subtype.eq ; simp ; apply Iff.mp List.ofFn_inj ; simp ; norm_num
      rw [hrotxx, hrotb1b2]
      apply And.intro hx heq.right.right

/- Step 3: Result of `kochen_specker_step_2` implies existence of a `OneZeroOneFunc` that assigns `zero` to `x`, `b1`, and `b3` -/

theorem kochen_specker_step_3 (f : OneZeroOneFunc) (hx : apply f x = zero) (hb1 : apply f b1 = zero) :
  ∃ f : OneZeroOneFunc, apply f x = zero ∧ apply f b1 = zero ∧ apply f b3 = zero :=
by
  have ha1 : apply f a1 = one := by
    apply perp_zero_implies_one f x a1 hx perp_xa1
  have hin : [apply f a1, apply f b3, apply f b4] ∈ ValidThriples := f.property a1 b3 b4 perp_a1b3b4
  rw [ValidThriples] at hin ; simp at hin
  cases hin with
  | inl heq =>
    rw [heq.left] at ha1
    contradiction
  | inr heq => cases heq with
    | inl heq =>
      exact Exists.intro f (And.intro hx (And.intro hb1 heq.right.left))
    | inr heq =>
      apply Exists.intro (rotxyz_xzy.compose_OneZeroOneFunc f)
      repeat rw [O3.compose_OneZeroOneFunc] ; repeat rw [apply] ; simp
      have hrotxx : rotxyz_xzy.function x = x := by
        simp [O3.function, x, rotxyz_xzy]
        apply Subtype.eq ; exact Iff.mp List.ofFn_inj rfl
      have hrotb1b1 : rotxyz_xzy.function b1 = b1 := by
        simp [O3.function, b1, rotxyz_xzy]
        apply Subtype.eq ; simp ; apply Iff.mp List.ofFn_inj ; simp
      have hrotb3b4 : rotxyz_xzy.function b3 = b4 := by
        simp [O3.function, b3, b4, rotxyz_xzy]
        apply Subtype.eq ; simp ; apply Iff.mp List.ofFn_inj ; simp
      rw [hrotxx, hrotb1b1, hrotb3b4]
      apply And.intro hx (And.intro hb1 heq.right.right)

/- Step 4: Result of `kochen_specker_step_3` implies a contradiction -/

theorem kochen_specker_step_4 (f : OneZeroOneFunc) (hx : apply f x = zero) (hb1 : apply f b1 = zero) (hb3 : apply f b3 = zero) :
  False :=
by
  have hz : apply f z = one := by
    apply perp_zero_implies_one f x z hx perp_xz
  have hc1 : apply f c1 = one := by
    apply perp_zero_implies_one f b1 c1 hb1 perp_b1c1
  have hc2 : apply f c2 = one := by
    apply perp_zero_implies_one f b3 c2 hb3 perp_b3c2
  have hd1 : apply f d1 = zero := by
    apply perp_one_one_implies_zero f c1 z d1 (And.intro hc1 hz) perp_c1zd1
  have hd2 : apply f d2 = zero := by
    apply perp_one_one_implies_zero f c2 z d2 (And.intro hc2 hz) perp_c2zd2
  have he1 : apply f e1 = one := by
    apply perp_zero_implies_one f d1 e1 hd1 perp_d1e1
  have he2 : apply f e2 = one := by
    apply perp_zero_implies_one f d1 e2 hd1 perp_d1e2
  have he3 : apply f e3 = one := by
    apply perp_zero_implies_one f d2 e3 hd2 perp_d2e3
  have he4 : apply f e4 = one := by
    apply perp_zero_implies_one f d2 e4 hd2 perp_d2e4
  have hf1 : apply f f1  = zero := by
    apply perp_one_one_implies_zero f e2 e3 f1 (And.intro he2 he3) perp_e2e3f1
  have hf2 : apply f f2  = zero := by
    apply perp_one_one_implies_zero f e1 e4 f2 (And.intro he1 he4) perp_e1e4f2
  have hf2_contradiction : apply f f2  = one := by
    apply perp_zero_implies_one f f1 f2 hf1 perp_f1f2
  -- now we have zero = apply f f2 = one. Use this to show a contradiction
  rw [hf2] at hf2_contradiction
  contradiction

/-- Main Kochen-Specker theorem stating the `OneZeroOneFunc` type is empty.
The proof just chains the helper lemmas defined above -/

theorem kochen_specker :
  OneZeroOneFunc → False :=
by
  intro f
  cases (kochen_specker_step_1 f) with
  | intro f hx => cases (kochen_specker_step_2 f hx) with
    | intro f hxb1 => cases (kochen_specker_step_3 f hxb1.left hxb1.right) with
      | intro f hxb1b3 =>
        exact kochen_specker_step_4 f hxb1b3.left hxb1b3.right.left hxb1b3.right.right

end KochenSpeckerDeep
end Contextuality
end Noneism
end HeytingLean
