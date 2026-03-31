import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Relation algebra (axiomatic core)

A relation algebra is a Boolean algebra equipped with a composition operation
and a converse (involution) satisfying the standard equational axioms:
associativity and unit for composition, distribution over joins, and involutive
converse with reversal of composition.  This file provides an axiomatic
interface for integration and later specialization to concrete relational
models.
-/

namespace HeytingLean
namespace Logic

class RelationAlgebra (α : Type*) extends BooleanAlgebra α where
  comp : α → α → α
  one : α
  converse : α → α
  comp_assoc : ∀ a b c, comp (comp a b) c = comp a (comp b c)
  one_comp : ∀ a, comp one a = a
  comp_one : ∀ a, comp a one = a
  comp_sup_left : ∀ a b c, comp (a ⊔ b) c = comp a c ⊔ comp b c
  comp_sup_right : ∀ a b c, comp a (b ⊔ c) = comp a b ⊔ comp a c
  converse_invol : ∀ a, converse (converse a) = a
  converse_comp : ∀ a b, converse (comp a b) = comp (converse b) (converse a)
  converse_sup : ∀ a b, converse (a ⊔ b) = converse a ⊔ converse b

end Logic
end HeytingLean
