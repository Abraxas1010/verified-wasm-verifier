/-!
# MV-algebra (Łukasiewicz many-valued algebra)

We keep the MV-algebra definition axiomatic: a commutative monoid with a
negation operator satisfying the standard MV identities.  The constants are
`zero` (often written 0) and `one := neg zero`.
-/

namespace HeytingLean
namespace Logic

universe u

class MVAlgebra (α : Type u) where
  mvAdd : α → α → α
  mvNeg : α → α
  zero : α
  mvAdd_assoc : ∀ a b c, mvAdd (mvAdd a b) c = mvAdd a (mvAdd b c)
  mvAdd_comm : ∀ a b, mvAdd a b = mvAdd b a
  mvAdd_zero : ∀ a, mvAdd a zero = a
  mvNeg_invol : ∀ a, mvNeg (mvNeg a) = a
  mvAdd_neg_zero : ∀ a, mvAdd a (mvNeg zero) = mvNeg zero
  lukasiewicz : ∀ a b,
    mvAdd (mvNeg (mvAdd (mvNeg a) b)) b = mvAdd (mvNeg (mvAdd (mvNeg b) a)) a

end Logic
end HeytingLean
