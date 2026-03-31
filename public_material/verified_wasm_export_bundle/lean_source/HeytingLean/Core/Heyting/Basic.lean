import Mathlib.Order.Heyting.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic

namespace HeytingLean.Core.Heyting

abbrev HeytingAlgebra := _root_.HeytingAlgebra

/-- The nucleus (closure operator) on a Heyting algebra. -/
structure Nucleus (α : Type*) [HeytingAlgebra α] where
  op : α → α
  extensive : ∀ x, x ≤ op x
  idempotent : ∀ x, op (op x) = op x
  preserves_meet : ∀ x y, op (x ⊓ y) = op x ⊓ op y

end HeytingLean.Core.Heyting
