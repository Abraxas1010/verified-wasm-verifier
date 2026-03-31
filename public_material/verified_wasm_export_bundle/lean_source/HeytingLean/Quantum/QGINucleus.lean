import HeytingLean.LoF.PrimaryAlgebra

/-
QGI-style interior nucleus (lens) on top of a primary algebra.

This sits *alongside* `LoF.Reentry` and is intentionally weaker: it models a
domain-specific closure / interior operator with a singled-out “support”
configuration that plays the role of a minimal nontrivial stable set.

It does not participate directly in the Ωᴿ / Euler-boundary kernel and so can
be specialised for QGI use without changing the core LoF axioms.
-/

namespace HeytingLean
namespace Quantum

open LoF

universe u

/-- Interior-style nucleus for QGI-style configuration spaces.

This is deliberately weaker than `LoF.Reentry`: it only remembers a
distinguished non-bottom fixed point `support`, leaving stronger
minimality properties to model-specific assumptions. -/
structure QGINucleus (α : Type u) [PrimaryAlgebra α] where
  act      : α → α
  monotone : Monotone act
  idempotent : ∀ a, act (act a) = act a
  apply_le  : ∀ a, act a ≤ a
  map_inf   : ∀ a b, act (a ⊓ b) = act a ⊓ act b
  /-- Distinguished non-bottom stable configuration. -/
  support   : α
  support_mem : act support = support
  support_nonbot : ⊥ < support

namespace QGINucleus

variable {α : Type u} [PrimaryAlgebra α]

@[simp] lemma apply_inf (N : QGINucleus α) (a b : α) :
    N.act (a ⊓ b) = N.act a ⊓ N.act b :=
  N.map_inf a b

@[simp] lemma idem (N : QGINucleus α) (a : α) :
    N.act (N.act a) = N.act a :=
  N.idempotent a

@[simp] lemma apply_support (N : QGINucleus α) :
    N.act N.support = N.support :=
  N.support_mem

end QGINucleus

end Quantum
end HeytingLean
