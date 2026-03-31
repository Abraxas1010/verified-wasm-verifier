import HeytingLean.EpistemicCalculus.Basic
import HeytingLean.EpistemicCalculus.Axioms
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

namespace HeytingLean.EpistemicCalculus.Examples

/--
Certainty factors in odds coordinates:
`CF = {x : ℝ | 0 < x}`, fusion = multiplication, unit = `1`.
This is equivalent to the open-interval hyperbolic calculus through the standard odds map.
-/
abbrev CF := { x : ℝ // 0 < x }

def cfOne : CF := ⟨1, by norm_num⟩
def cfTwo : CF := ⟨2, by norm_num⟩

def cfFusion (x y : CF) : CF := ⟨x.1 * y.1, mul_pos x.2 y.2⟩

instance : EpistemicCalculus CF where
  fusion := cfFusion
  unit := cfOne
  fusion_assoc := by
    intro x y z
    apply Subtype.ext
    simp [cfFusion, mul_assoc]
  fusion_comm := by
    intro x y
    apply Subtype.ext
    simp [cfFusion, mul_comm]
  fusion_unit_left := by
    intro x
    apply Subtype.ext
    simp [cfFusion, cfOne]
  fusion_mono := by
    intro x x' y y' hx hy
    change x.1 * y.1 ≤ x'.1 * y'.1
    exact mul_le_mul hx hy (le_of_lt y.2) (le_of_lt x'.2)
  nontrivial := by
    refine ⟨cfOne, cfTwo, ?_⟩
    intro h
    have hval : (cfOne : ℝ) = (cfTwo : ℝ) := congrArg Subtype.val h
    norm_num [cfOne, cfTwo] at hval

noncomputable instance : Closed CF where
  ihom := fun y z => ⟨z.1 / y.1, div_pos z.2 y.2⟩
  adjunction := by
    intro x y z
    change x.1 * y.1 ≤ z.1 ↔ x.1 ≤ z.1 / y.1
    constructor
    · intro h
      exact (le_div_iff₀ y.2).2 h
    · intro h
      exact (le_div_iff₀ y.2).1 h

noncomputable instance : Fallible CF where
  revisable := by
    intro x y
    refine ⟨⟨y.1 / x.1, div_pos y.2 x.2⟩, ?_⟩
    change x.1 * (y.1 / x.1) ≤ y.1
    have hx : x.1 ≠ 0 := ne_of_gt x.2
    have hEq : x.1 * (y.1 / x.1) = y.1 := by
      calc
        x.1 * (y.1 / x.1) = (x.1 * y.1) / x.1 := by
          exact (mul_div_assoc x.1 y.1 x.1).symm
        _ = y.1 := by
          exact mul_div_cancel_left₀ y.1 hx
    exact le_of_eq hEq

end HeytingLean.EpistemicCalculus.Examples
