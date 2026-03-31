import HeytingLean.Bridges.JRatchet.Extensions.NuclearRangeRatchet
import Mathlib.Data.Fintype.Basic

/-!
# DiegoFiniteness

This module packages finite-search consequences of
Bezhanishvili et al. (2020) for nuclear implicative semilattices.

Deep local-finiteness content is introduced as an attributed axiomized bridge.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet
namespace Extensions
namespace DiegoFiniteness

open NuclearRangeRatchet

universe u

/-- Nuclear implicative semilattice with a distinguished semilattice nucleus. -/
class NuclearImplicativeSemilattice (α : Type u)
    extends ImplicativeSemilattice α where
  /-- Distinguished nucleus action. -/
  nucleus : α → α
  /-- Extensiveness of the designated nucleus. -/
  nucleus_extensive : ∀ a, a ≤ nucleus a
  /-- Meet-preservation of the designated nucleus. -/
  nucleus_map_inf : ∀ a b, nucleus (a ⊓ b) = nucleus a ⊓ nucleus b
  /-- Idempotence of the designated nucleus. -/
  nucleus_idempotent : ∀ a, nucleus (nucleus a) = nucleus a

/-- Canonical semilattice nucleus extracted from `NuclearImplicativeSemilattice`. -/
def designatedSemilatticeNucleus
    {α : Type u} [NuclearImplicativeSemilattice α] :
    SemilatticeNucleus α where
  act := NuclearImplicativeSemilattice.nucleus
  extensive := NuclearImplicativeSemilattice.nucleus_extensive
  map_inf := NuclearImplicativeSemilattice.nucleus_map_inf
  idempotent := NuclearImplicativeSemilattice.nucleus_idempotent

/--
AXIOM (Bezhanishvili et al. 2020, local-finiteness main theorem):
for finite carriers, the nucleus space is finite.
-/
axiom diego_finiteness
  {α : Type u} [NuclearImplicativeSemilattice α] [Fintype α] :
  Finite (SemilatticeNucleus α)

/-- Finite carrier consequence: ratchet-step candidate space is finite. -/
theorem finiteRatchetStepEnumerable
  {α : Type u} [NuclearImplicativeSemilattice α] [Fintype α] [DecidableEq α] :
  Finite { f : α → α //
    ∀ a : α,
      a ≤ f a ∧ f (a ⊓ a) = f a ⊓ f a ∧ f (f a) = f a } := by
  classical
  infer_instance

/-- Decidable equality on finite ratchet-step candidate codes. -/
noncomputable instance allRatchetStepsDecidable
  {α : Type u} [NuclearImplicativeSemilattice α] [Fintype α] [DecidableEq α] :
  DecidableEq { f : α → α //
    ∀ a : α,
      a ≤ f a ∧ f (a ⊓ a) = f a ⊓ f a ∧ f (f a) = f a } := by
  classical
  infer_instance

end DiegoFiniteness
end Extensions
end JRatchet
end Bridges
end HeytingLean
