import Mathlib.Order.Nucleus

open scoped Classical

namespace HeytingLean.Quantum.Translate

variable {α : Type _} [CompleteLattice α]

structure Modality (α : Type _) [CompleteLattice α] where
  J : Nucleus α
  preserves_top : J ⊤ = (⊤ : α)

namespace Modality

variable (M : Modality α)

def close : α → α := M.J

@[simp] lemma close_apply (a : α) : M.close a = M.J a := rfl

@[simp] lemma idempotent (a : α) : M.close (M.close a) = M.close a := M.J.idempotent _

@[simp] lemma map_inf (a b : α) : M.close (a ⊓ b) = M.close a ⊓ M.close b :=
  Nucleus.map_inf (n := M.J) (x := a) (y := b)

lemma map_sup (a b : α) : M.close (a ⊔ b) = M.close (M.close a ⊔ M.close b) := by
  classical
  simpa using (M.J.toClosureOperator.closure_sup_closure (x := a) (y := b)).symm

/-- Closing a right summand before joining does not change the overall closure. -/
lemma sup_close_right (M : Modality α) (x y : α) :
    M.close (x ⊔ M.close y) = M.close (x ⊔ y) := by
  apply le_antisymm
  ·
    -- `x ⊔ M.close y` already lies under the desired closure.
    have hx : x ≤ M.close (x ⊔ y) := by
      have hx' : x ≤ x ⊔ y := le_sup_left
      have hx'' := M.J.monotone hx'
      exact (Nucleus.le_apply (n := M.J) (x := x)).trans hx''
    have hy : M.close y ≤ M.close (x ⊔ y) := by
      have hy' : y ≤ x ⊔ y := le_sup_right
      have hy'' := M.J.monotone hy'
      simpa using hy''
    have h := sup_le hx hy
    have h' := M.J.monotone h
    simpa [Modality.close, Modality.idempotent] using h'
  ·
    have h_base : x ⊔ y ≤ x ⊔ M.close y :=
      sup_le_sup_left (Nucleus.le_apply (n := M.J) (x := y)) _
    have h := M.J.monotone h_base
    simpa [Modality.close] using h

/-- Symmetric variant of `sup_close_right`. -/
lemma sup_close_left (M : Modality α) (x y : α) :
    M.close (M.close x ⊔ y) = M.close (x ⊔ y) := by
  simpa [sup_comm] using (M.sup_close_right (x := y) (y := x))

/-! ### Identity modality -/

/-- The identity nucleus on any inf-semilattice. -/
@[simp] def idNucleus (α : Type _) [SemilatticeInf α] : Nucleus α :=
{ toInfHom :=
    { toFun := id
      map_inf' := by intro _ _; rfl }
  idempotent' := by intro _; exact le_rfl
  le_apply' := by intro _; exact le_rfl }

/-- The trivial modality whose nucleus is the identity. -/
@[simp] def id (α : Type _) [CompleteLattice α] : Modality α :=
{ J := idNucleus α
  preserves_top := by simp [idNucleus] }

@[simp] lemma id_close (α : Type _) [CompleteLattice α] (a : α) :
    (Modality.id α).close a = a := rfl

end Modality

end HeytingLean.Quantum.Translate
