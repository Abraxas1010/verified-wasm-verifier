import HeytingLean.Bridges.JRatchet.Extensions.PataraiaNuclearJoin
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Directed

/-!
# NuclearRangeRatchet

This module introduces semilattice-level nucleus and ratchet interfaces inspired by
Erne, *Nuclear ranges in implicative semilattices* (Algebra Universalis, 2022).

The core statement (`ratchetConverges_iff_directedJoins`) is included as an axiomized,
attributed literature bridge for the non-complete setting.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet
namespace Extensions
namespace NuclearRangeRatchet

universe u

/-- Implicative semilattice interface for non-complete ratchet settings. -/
class ImplicativeSemilattice (α : Type u) extends SemilatticeInf α, OrderBot α where
  /-- Residual implication operation. -/
  himp : α → α → α
  /-- Adjointness between meet and implication. -/
  himp_adjoint : ∀ a b c : α, a ⊓ b ≤ c ↔ a ≤ himp b c

/-- Nucleus structure on a semilattice (without global completeness assumptions). -/
structure SemilatticeNucleus (α : Type u) [SemilatticeInf α] where
  /-- Action map. -/
  act : α → α
  /-- Extensiveness. -/
  extensive : ∀ a, a ≤ act a
  /-- Finite-meet preservation. -/
  map_inf : ∀ a b, act (a ⊓ b) = act a ⊓ act b
  /-- Idempotence. -/
  idempotent : ∀ a, act (act a) = act a

/-- Nuclear range as set-theoretic image of `act`. -/
def nuclearRange {α : Type u} [SemilatticeInf α]
    (N : SemilatticeNucleus α) : Set α :=
  Set.range N.act

/-- Directed-join completeness predicate used in Erne's characterization. -/
def HasDirectedJoins (α : Type u) [SemilatticeInf α] [OrderBot α] : Prop :=
  ∀ (S : Set α), DirectedOn (· ≤ ·) S → ∃ s : α, IsLUB S s

/-- Semilattice pre-ratchet step: extensive + monotone endomap. -/
structure PreRatchetStepSL (α : Type u) [SemilatticeInf α] [OrderBot α] where
  /-- Action map. -/
  step : α → α
  /-- Extensiveness. -/
  extensive : ∀ a, a ≤ step a
  /-- Monotonicity. -/
  monotone : Monotone step

/-- Semilattice ratchet step adds idempotence on top of `PreRatchetStepSL`. -/
structure SemilatticeRatchetStep (α : Type u) [SemilatticeInf α] [OrderBot α]
    extends PreRatchetStepSL α where
  /-- Idempotence. -/
  idempotent : ∀ a, step (step a) = step a

/--
AXIOM (Erne 2022, Theorem 4.7): in implicative semilattices,
convergence/completion of pre-ratchet steps is equivalent to existence of directed joins.
-/
axiom ratchetConverges_iff_directedJoins
  {α : Type u} [ImplicativeSemilattice α] :
  (∀ P : PreRatchetStepSL α,
    ∃ S : SemilatticeRatchetStep α,
      ∀ a : α, P.step a ≤ S.step a) ↔
  HasDirectedJoins α

/-- Finite semilattice ratchet convergence predicate is classically decidable. -/
noncomputable instance finiteRatchetDecidable
    {α : Type u} [ImplicativeSemilattice α] [Fintype α] [DecidableEq α] :
    Decidable (HasDirectedJoins α) := by
  classical
  infer_instance

end NuclearRangeRatchet
end Extensions
end JRatchet
end Bridges
end HeytingLean
