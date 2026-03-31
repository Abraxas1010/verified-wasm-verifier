import HeytingLean.LoF.Nucleus

/-
CTMU Core scaffold (library-only): reuse Reentry/Stable and define
Telesis and a UniverseSpec record. Also include Sufficient and
OccamOptimal predicates aligned with PSR/Occam language.
-/

namespace HeytingLean
namespace CTMU

open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

abbrev Stable (R : Reentry α) := { x : α // R x = x }
abbrev Telesis (R : Reentry α) := { x : α // R x ≠ x }

structure UniverseSpec (R : Reentry α) where
  carrier : α
  isFixed : R carrier = carrier
  maximal : ∀ {y : α}, R y = y → y ≤ carrier

@[simp] def Sufficient (R : Reentry α) (x : α) : Prop := R x = x

@[simp] def OccamOptimal (R : Reentry α) (x : Stable R) : Prop :=
  ∀ {y : α}, Sufficient R y → x.1 ≤ y

end CTMU
end HeytingLean

