import Mathlib.Order.CompleteLattice.Defs

/-!
# LoF ClosureCore — closure-only re-entry façade

This module provides a lightweight, closure-only alternative to `Reentry`.
It packages an extensive, monotone, idempotent operator `act : α → α` without
requiring finite-meet preservation. The fixed points `Ω_R` support order-level
reasoning; however, they do not inherit a Heyting algebra unless additional
meet-preservation laws are provided (i.e., a true `Nucleus`).
-/

namespace HeytingLean
namespace LoF

universe u

variable {α : Type u} [CompleteLattice α]

/-- Closure-style core: extensive, monotone, idempotent. -/
structure ClosureCore (α : Type u) [CompleteLattice α] where
  act : α → α
  monotone : Monotone act
  le_apply : ∀ a, a ≤ act a
  idempotent : ∀ a, act (act a) = act a

namespace ClosureCore

variable (R : ClosureCore α)

instance : CoeFun (ClosureCore α) (fun _ => α → α) where
  coe R := R.act

@[simp] lemma apply_le (a : α) : a ≤ R a := R.le_apply a
@[simp] lemma idem (a : α) : R (R a) = R a := R.idempotent a
lemma mono : Monotone R := R.monotone

/-- Fixed points of the closure. (No Heyting instance in general.) -/
abbrev Omega : Type u := {a : α // R a = a}

namespace Omega

variable {R}

def mk (a : α) (h : R a = a) : R.Omega := ⟨a, h⟩

@[simp] lemma coe_mk (a : α) (h : R a = a) : ((mk (R := R) a h : R.Omega) : α) = a := rfl

@[simp] lemma apply_coe (a : R.Omega) : R (a : α) = a := by simpa using a.property

end Omega

end ClosureCore

end LoF
end HeytingLean
