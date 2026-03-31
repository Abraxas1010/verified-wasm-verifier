import Mathlib.Order.Nucleus
import HeytingLean.LoF.IntReentry
import HeytingLean.Quantum.QGINucleus

namespace HeytingLean
namespace Bridges
namespace Nucleus

open HeytingLean.LoF
open HeytingLean.Quantum

universe u

/-- Drop `QGINucleus` support data to get an `IntNucleus`. -/
def qgiToInt {α : Type u} [PrimaryAlgebra α]
    (N : QGINucleus α) : IntNucleus α where
  act := N.act
  monotone := N.monotone
  idempotent := N.idempotent
  apply_le := N.apply_le
  map_inf := N.map_inf

/-- Promote an `IntNucleus` to `QGINucleus` once a support witness is supplied. -/
def intToQgiWithSupport {α : Type u} [PrimaryAlgebra α]
    (N : IntNucleus α)
    (support : α)
    (support_mem : N.act support = support)
    (support_nonbot : ⊥ < support) : QGINucleus α where
  act := N.act
  monotone := N.monotone
  idempotent := N.idempotent
  apply_le := N.apply_le
  map_inf := N.map_inf
  support := support
  support_mem := support_mem
  support_nonbot := support_nonbot

/-- Dropping support after supported promotion recovers the original interior nucleus. -/
theorem qgiToInt_intToQgiWithSupport {α : Type u} [PrimaryAlgebra α]
    (N : IntNucleus α)
    (support : α)
    (support_mem : N.act support = support)
    (support_nonbot : ⊥ < support) :
    qgiToInt (intToQgiWithSupport N support support_mem support_nonbot) = N := by
  rfl

/-- Re-promoting a `QGINucleus` with its own support is definitional identity. -/
theorem intToQgiWithSupport_qgiToInt {α : Type u} [PrimaryAlgebra α]
    (N : QGINucleus α) :
    intToQgiWithSupport (qgiToInt N) N.support N.support_mem N.support_nonbot = N := by
  cases N
  rfl

section ClosureInteriorDuality

variable {α : Type u} [BooleanAlgebra α]

/-- Candidate interior action induced from closure by complementation. -/
def closureDualAct (N : _root_.Nucleus α) (a : α) : α := (N aᶜ)ᶜ

/-- The closure-dual action is monotone. -/
theorem closureDualAct_monotone (N : _root_.Nucleus α) :
    Monotone (closureDualAct N) := by
  intro a b hab
  exact compl_le_compl (_root_.Nucleus.monotone (n := N) (compl_le_compl hab))

/-- The closure-dual action is deflationary. -/
theorem closureDualAct_apply_le (N : _root_.Nucleus α) (a : α) :
    closureDualAct N a ≤ a := by
  have h : aᶜ ≤ N aᶜ := _root_.Nucleus.le_apply (n := N) (x := aᶜ)
  simpa [closureDualAct] using compl_le_compl h

/-- Idempotence of the closure-dual action, assuming closure also preserves joins. -/
theorem closureDualAct_idempotent_of_map_sup
    (N : _root_.Nucleus α)
    (a : α) :
    closureDualAct N (closureDualAct N a) = closureDualAct N a := by
  simp [closureDualAct, _root_.Nucleus.idempotent]

/-- Meet preservation of the closure-dual action, assuming closure preserves joins. -/
theorem closureDualAct_map_inf_of_map_sup
    (N : _root_.Nucleus α)
    (hmap_sup : ∀ a b, N (a ⊔ b) = N a ⊔ N b)
    (a b : α) :
    closureDualAct N (a ⊓ b) = closureDualAct N a ⊓ closureDualAct N b := by
  simp [closureDualAct, hmap_sup]

end ClosureInteriorDuality

end Nucleus
end Bridges
end HeytingLean
