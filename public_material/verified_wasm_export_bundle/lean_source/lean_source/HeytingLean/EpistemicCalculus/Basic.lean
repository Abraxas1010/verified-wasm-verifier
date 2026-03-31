import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Real.Basic

namespace HeytingLean

/--
An epistemic calculus in algebra-first form:
a partial order with a commutative, associative, monotone fusion operation and a unit.
-/
class EpistemicCalculus (V : Type*) extends PartialOrder V where
  fusion : V → V → V
  unit : V
  fusion_assoc : ∀ x y z : V, fusion (fusion x y) z = fusion x (fusion y z)
  fusion_comm : ∀ x y : V, fusion x y = fusion y x
  fusion_unit_left : ∀ x : V, fusion unit x = x
  fusion_mono :
    ∀ {x x' y y' : V}, x ≤ x' → y ≤ y' → fusion x y ≤ fusion x' y'
  nontrivial : ∃ x y : V, x ≠ y

scoped infixl:70 " fus " => EpistemicCalculus.fusion

variable {V : Type*} [EpistemicCalculus V]

@[simp] theorem fusion_unit_right (x : V) :
    x fus EpistemicCalculus.unit = x := by
  rw [EpistemicCalculus.fusion_comm, EpistemicCalculus.fusion_unit_left]

theorem fusion_mono_left {x x' y : V} (h : x ≤ x') :
    x fus y ≤ x' fus y := by
  exact EpistemicCalculus.fusion_mono h le_rfl

theorem fusion_mono_right {x y y' : V} (h : y ≤ y') :
    x fus y ≤ x fus y' := by
  exact EpistemicCalculus.fusion_mono le_rfl h

theorem fusion_mono' {x x' y y' : V} (hx : x ≤ x') (hy : y ≤ y') :
    x fus y ≤ x' fus y' := by
  exact EpistemicCalculus.fusion_mono hx hy

end HeytingLean
