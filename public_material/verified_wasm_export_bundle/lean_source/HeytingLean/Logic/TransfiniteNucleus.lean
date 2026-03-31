import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Heyting.Basic
import HeytingLean.LoF.Nucleus
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Transfinite (ω-staged) iteration of a nucleus

This module provides a lightweight, computable core for iterating a `Nucleus α`
over a complete lattice `α`. It focuses on the ω-fragment (finite iteration),
which is sufficient for executable QA and for a first OFI implementation. A
future extension can lift these definitions to true ordinal iteration.
-/

namespace HeytingLean
namespace Logic

variable {α : Type*}

section IterateNat

variable [SemilatticeInf α]

/-- Apply a nucleus `R` to `x` exactly `n` times. -/
def iterateNat (R : Nucleus α) : Nat → α → α
  | 0,     x => x
  | n+1,   x => R (iterateNat R n x)

@[simp] lemma iterateNat_zero (R : Nucleus α) (x : α) : iterateNat R 0 x = x := rfl
@[simp] lemma iterateNat_succ (R : Nucleus α) (n : Nat) (x : α)
  : iterateNat R (n+1) x = R (iterateNat R n x) := rfl

end IterateNat

section OmegaLimit

variable [CompleteLattice α]

/-- The ω-limit of iterates of `R` starting from `x`: `⨆ n, R^n x`. -/
noncomputable def omegaSup (R : Nucleus α) (x : α) : α :=
  sSup (Set.range (fun n : Nat => iterateNat R n x))

/-- One more step after the ω-limit. Useful to test for post-ω stabilization. -/
noncomputable def omegaSucc (R : Nucleus α) (x : α) : α :=
  R (omegaSup R x)

end OmegaLimit

section OmegaLemmas

variable [CompleteLattice α]

/-- The ω-limit is below its successor application. -/
lemma omegaSup_le_omegaSucc (R : Nucleus α) (x : α) :
    omegaSup (α := α) R x ≤ omegaSucc (α := α) R x := by
  change omegaSup (α := α) R x ≤ R (omegaSup (α := α) R x)
  exact (Nucleus.le_apply (n := R) (x := omegaSup (α := α) R x))

end OmegaLemmas

-- NOTE: A full ordinal transfinite iterator is deferred for a future proof-oriented module.

-- (Further finite stabilization lemmas can be added here when needed.)

end Logic
end HeytingLean
