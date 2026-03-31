import HeytingLean.Logic.ResiduatedCore

/-!
# Residuated lattice (commutative, bounded)

This file defines a commutative, bounded residuated lattice on top of the
minimal `ResiduatedCore` interface.  It is intentionally lightweight: we add
only a unit and the commutative-monoid laws for `mul`.  This matches the
algebraic setting commonly used for BL-algebras.
-/

namespace HeytingLean
namespace Logic

class ResiduatedLattice (α : Type*) extends ResiduatedCore α where
  one : α
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a

end Logic
end HeytingLean
