import HeytingLean.Calculus.RModalCalculus

/-!
# Leibniz layer (Phase 3): PSR, Occam, fictions

We encode these as lightweight predicates over an `RModal` carrier. This keeps
proofs minimal while providing named hooks for later extensions.
-/

namespace HeytingLean
namespace Calculus

universe u

variable {α : Type u} [CompleteLattice α]

structure LeibnizAxioms (M : RModal α) : Type where
  /-- Principle of sufficient reason holds (assumption hook). -/
  psr : Prop
  /-- Parsimony preference (assumption hook). -/
  occam : Prop
  /-- Well-founded fictions admissible (assumption hook). -/
  fict : Prop

namespace LeibnizAxioms

variable {M : RModal α}

@[simp] def stable (L : LeibnizAxioms M) : Prop := L.psr ∧ L.occam ∧ L.fict

@[simp] theorem stable_intro {L : LeibnizAxioms M}
    (h1 : L.psr) (h2 : L.occam) (h3 : L.fict) : stable L := And.intro h1 (And.intro h2 h3)

end LeibnizAxioms

end Calculus
end HeytingLean
