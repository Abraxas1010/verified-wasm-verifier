import Mathlib/Order/Nucleus

open scoped Classical

namespace HeytingLean.LoF.Lens.Truncation

/-! # Axiomatic `n`‑Truncation Modality

We axiomatize a family of modalities indexed by a natural number. Each level
`n` is represented by a nucleus `τ` on a complete lattice. We do not model the
HoTT universe here — only the algebraic closure laws needed by our lenses.
-/

variable {α : Type _} [CompleteLattice α]

structure Level (α : Type _) [CompleteLattice α] where
  n : Nat
  τ : Nucleus α
  preserves_top : τ ⊤ = (⊤ : α)

namespace Level

variable (L : Level α)

@[simp] def J : α → α := L.τ

@[simp] lemma idempotent (a : α) : L.J (L.J a) = L.J a := L.τ.idempotent _

@[simp] lemma map_inf (a b : α) : L.J (a ⊓ b) = L.J a ⊓ L.J b :=
  Nucleus.map_inf (n := L.τ) (x := a) (y := b)

lemma map_sup (a b : α) : L.J (a ⊔ b) = L.J (L.J a ⊔ L.J b) := by
  classical
  simpa using (L.τ.toClosureOperator.closure_sup_closure (x := a) (y := b)).symm

end Level

end HeytingLean.LoF.Lens.Truncation

