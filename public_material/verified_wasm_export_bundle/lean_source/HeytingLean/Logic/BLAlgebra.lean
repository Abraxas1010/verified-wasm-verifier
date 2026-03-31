import HeytingLean.Logic.ResiduatedLattice

/-!
# BL-algebra (Basic Logic algebra)

A BL-algebra is a commutative, integral, bounded residuated lattice satisfying
divisibility and prelinearity.  We keep the definition axiomatic to avoid
coupling it to any specific representation.
-/

namespace HeytingLean
namespace Logic

class BLAlgebra (α : Type*) extends ResiduatedLattice α where
  integral : one = ⊤
  divisibility : ∀ a b, a ⊓ b = mul a (res a b)
  prelinearity : ∀ a b, res a b ⊔ res b a = ⊤

namespace BLAlgebra

variable {α : Type*} [BLAlgebra α]

lemma integral_top : ResiduatedLattice.one = (⊤ : α) :=
  BLAlgebra.integral

lemma divisibility_lemma (a b : α) :
    a ⊓ b = ResiduatedCore.mul a (ResiduatedCore.res a b) :=
  BLAlgebra.divisibility a b

lemma prelinearity_lemma (a b : α) :
    ResiduatedCore.res a b ⊔ ResiduatedCore.res b a = (⊤ : α) :=
  BLAlgebra.prelinearity a b

end BLAlgebra

end Logic
end HeytingLean
