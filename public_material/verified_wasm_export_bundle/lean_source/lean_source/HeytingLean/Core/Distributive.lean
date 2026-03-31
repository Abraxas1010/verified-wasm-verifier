import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Heyting.Basic

/-!
# Distributive Lattice Foundations (bundle core)

This module is intentionally small: it primarily re-exports Mathlib’s
distributive/Heyting lattice interface, and introduces a minimal “frame-style”
infinite distributivity hook for later development.
-/

namespace HeytingLean
namespace Core

/-- A lightweight “frame-style” distributivity predicate.

We keep this as a `Prop`-class so it can be supplied by `infer_instance` when
available, but it does not attempt to repackage the whole `Frame` API.
-/
class FrameDistributive (L : Type*) [CompleteLattice L] : Prop where
  /-- Infinite distributivity over `sSup`. -/
  inf_sSup_eq :
    ∀ (a : L) (s : Set L),
      a ⊓ sSup s = sSup (Set.image (fun b => a ⊓ b) s)

/-- Every Heyting algebra is a distributive lattice. -/
example {L : Type*} [HeytingAlgebra L] : DistribLattice L :=
  inferInstance

end Core
end HeytingLean
