import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.OmegaCategory
import HeytingLean.LoF.Rosetta.Core

/-
# RosettaSanity: basic checks for Ω_R Rosetta API

This module provides small, fully total sanity checks that:

* the Rosetta column aliases reduce to the underlying category-theoretic
  morphisms on `Ω_R`; and
* the Rosetta internal-hom notation `⊸ᵣ` agrees with the existing Heyting
  residuation law on `Ω_R`.
-/

namespace HeytingLean
namespace Tests
namespace LoF
namespace RosettaSanity

open HeytingLean.LoF
open HeytingLean.LoF.Rosetta

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- Rosetta propositions and proofs are just objects and morphisms in `Ω_R`. -/
example (R : Reentry α) (A B : Rosetta.Proposition (R := R)) :
    Rosetta.Proof (R := R) A B = (A ⟶ B) :=
  rfl

/-- Rosetta systems and processes are aliases for the same Ω_R objects/morphisms. -/
example (R : Reentry α) (A B : Rosetta.System (R := R)) :
    Rosetta.Process (R := R) A B = (A ⟶ B) :=
  rfl

/-- The internal hom on Ω_R (Heyting implication) satisfies the residuation law. -/
example (R : Reentry α) (a b c : R.Omega) :
    c ≤ a ⇨ b ↔ c ⊓ a ≤ b := by
  exact Reentry.residuation (R := R) (a := a) (b := b) (c := c)

end RosettaSanity
end LoF
end Tests
end HeytingLean
