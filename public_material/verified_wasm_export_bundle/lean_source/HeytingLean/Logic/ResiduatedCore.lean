import Mathlib.Order.Heyting.Basic

/-!
# Residuated core (minimal interface)

This file introduces a light-weight residuation interface intended to capture the
adjunction that underlies Heyting implication without refactoring the existing
Heyting-algebra hierarchy.  It is intentionally small: a bounded lattice with a
binary operation `mul` and a residual `res` satisfying the adjunction

`mul a b ≤ c ↔ b ≤ res a c`.

The primary goal is to make the Heyting core an instance of this interface,
providing a stable bridge for later BL/MV layers without destabilizing the
existing LoF/nucleus pipeline.
-/

namespace HeytingLean
namespace Logic

/-- Minimal residuation interface (bounded lattice + adjoint residual). -/
class ResiduatedCore (α : Type*) extends Lattice α, Top α, Bot α where
  mul : α → α → α
  res : α → α → α
  residuation : ∀ a b c, mul a b ≤ c ↔ b ≤ res a c

namespace ResiduatedCore

variable {α : Type*} [ResiduatedCore α]

@[simp] lemma mul_le_iff (a b c : α) :
    ResiduatedCore.mul a b ≤ c ↔ b ≤ ResiduatedCore.res a c :=
  ResiduatedCore.residuation a b c

end ResiduatedCore

/-- Heyting algebras are integral residuated cores with `mul = inf` and `res = himp`. -/
instance instResiduatedCoreOfHeyting (α : Type*) [HeytingAlgebra α] :
    ResiduatedCore α where
  mul := (· ⊓ ·)
  res := (· ⇨ ·)
  residuation := by
    intro a b c
    -- `b ≤ a ⇨ c ↔ a ⊓ b ≤ c`
    simpa using (le_himp_iff' (a := b) (b := a) (c := c)).symm

end Logic
end HeytingLean
