import Mathlib/Order/Nucleus

open scoped Classical

namespace HeytingLean.LoF.Lens.SheafLT

/-! # Axiomatic Lawvere–Tierney Modality

We model a modality as a nucleus `j` on a complete lattice together with
`j ⊤ = ⊤`. The nucleus gives us idempotence, monotonicity, and
meet‑preservation out of the box; we expose convenient lemmas mirroring the
closure/interior behavior required by the lenses framework.
-/

variable {α : Type _} [CompleteLattice α]

structure Modality (α : Type _) [CompleteLattice α] where
  j : Nucleus α
  preserves_top : j ⊤ = (⊤ : α)

namespace Modality

variable (M : Modality α)

@[simp] def J : α → α := M.j

@[simp] lemma idempotent (a : α) : M.J (M.J a) = M.J a := M.j.idempotent _

@[simp] lemma le_apply (a : α) : a ≤ M.J a := Nucleus.le_apply (n := M.j) (x := a)

@[simp] lemma map_inf (a b : α) : M.J (a ⊓ b) = M.J a ⊓ M.J b :=
  Nucleus.map_inf (n := M.j) (x := a) (y := b)

lemma map_sup (a b : α) : M.J (a ⊔ b) = M.J (M.J a ⊔ M.J b) := by
  classical
  simpa using (M.j.toClosureOperator.closure_sup_closure (x := a) (y := b)).symm

lemma map_sup_le (a b : α) : M.J a ⊔ M.J b ≤ M.J (a ⊔ b) := by
  classical
  exact M.j.toClosureOperator.closure_sup_closure_le (x := a) (y := b)

end Modality

end HeytingLean.LoF.Lens.SheafLT

