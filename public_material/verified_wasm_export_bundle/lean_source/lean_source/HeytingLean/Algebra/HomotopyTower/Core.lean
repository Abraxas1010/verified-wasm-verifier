import Mathlib.Order.Nucleus
import Mathlib.Order.Monotone.Basic
import HeytingLean.LoF.Combinators.Heyting.FixedPointHeyting
import HeytingLean.PerspectivalPlenum.ReReentryTower

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

open Set

universe u

variable {α : Type u} [Order.Frame α]

/-- An ascending tower of nuclei on a frame. -/
structure NucleusTower where
  level : Nat → Nucleus α
  mono : Monotone level

/-- The moved-point boundary of a nucleus. -/
def boundary (J : Nucleus α) : Set α := {x | J x ≠ x}

@[simp] theorem mem_boundary_iff (J : Nucleus α) (x : α) :
    x ∈ boundary J ↔ J x ≠ x :=
  Iff.rfl

/-- If `J ≤ K`, every `K`-fixed point is already `J`-fixed. -/
theorem fixed_eq_of_le {J K : Nucleus α} (hJK : J ≤ K) {x : α} (hx : K x = x) :
    J x = x := by
  apply le_antisymm
  · calc
      J x ≤ K x := hJK x
      _ = x := hx
  · exact J.le_apply

/-- Fixed points are antitone with respect to the pointwise order on nuclei. -/
theorem fixedPoints_antitone {J K : Nucleus α} (hJK : J ≤ K) :
    {x : α | K x = x} ⊆ {x : α | J x = x} := by
  intro x hx
  exact fixed_eq_of_le hJK hx

/-- The moved-point boundary is monotone increasing along the nucleus order. -/
theorem boundary_mono {J K : Nucleus α} (hJK : J ≤ K) :
    boundary J ⊆ boundary K := by
  intro x hx hKx
  exact hx (fixed_eq_of_le hJK hKx)

/-- A `RatchetTower` gives a special case of an ascending nucleus tower. -/
def ofRatchetTower (T : PerspectivalPlenum.RatchetTower α) : NucleusTower (α := α) where
  level := fun n => T.layer n
  mono := by
    apply monotone_nat_of_le_succ
    intro n
    simpa [PerspectivalPlenum.RatchetTower.layer_succ] using T.step.extensive (T.layer n)

end HomotopyTower
end Algebra
end HeytingLean
