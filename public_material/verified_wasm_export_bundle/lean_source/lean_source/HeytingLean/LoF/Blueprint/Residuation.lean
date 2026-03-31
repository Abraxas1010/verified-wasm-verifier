import HeytingLean.LoF.HeytingCore

/-
# LoF blueprint: residuation in Ω_R

This module packages the Heyting residuation law on the fixed-point core `Ω_R`
of a re-entry nucleus `R` into a small blueprint-style structure.
-/

namespace HeytingLean
namespace LoF
namespace Blueprint

open HeytingLean.LoF.Reentry

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- Blueprint record for residuation at fixed points `a b c : Ω_R`. -/
structure ResiduationBlueprint (R : Reentry α) (a b c : R.Omega) where
  /-- Forward direction: from `a ⊓ b ≤ c` to `a ≤ b ⇨ c`. -/
  forward  : a ⊓ b ≤ c → a ≤ b ⇨ c
  /-- Backward direction: from `a ≤ b ⇨ c` to `a ⊓ b ≤ c`. -/
  backward : a ≤ b ⇨ c → a ⊓ b ≤ c

/-- Build a residuation blueprint directly from the Heyting adjunction on `Ω_R`. -/
def mkResiduationBlueprint (R : Reentry α) (a b c : R.Omega) :
    ResiduationBlueprint (R := R) a b c :=
  { forward  := (Reentry.heyting_adjunction (R := R) a b c).mp
    backward := (Reentry.heyting_adjunction (R := R) a b c).mpr }

/-- Residuation equivalence on `Ω_R` (alias of `Reentry.heyting_adjunction`). -/
lemma residuation_equiv (R : Reentry α) (a b c : R.Omega) :
    a ⊓ b ≤ c ↔ a ≤ b ⇨ c :=
  Reentry.heyting_adjunction (R := R) a b c

end Blueprint
end LoF
end HeytingLean

