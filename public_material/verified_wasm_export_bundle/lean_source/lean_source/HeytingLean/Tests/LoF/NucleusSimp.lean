import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.HeytingCore

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

variable (R : Reentry α)
variable (a b c : R.Omega)

/-!
Compile-only sanity for the direct path (LoF → Heyting):
- Fixed points `Ω_R` carry a Heyting algebra;
- Residuation/adjunction lemma is available.
-/

-- Heyting instance exists on Ω_R
#check (inferInstance : HeytingAlgebra (R.Omega))

-- Adjunction (residuation) holds: a ⊓ b ≤ c ↔ a ≤ b ⇒ c
#check (Reentry.heyting_adjunction (R := R) a b c)

-- Double-negation inequality in Ω_R: a ≤ ¬¬a
example : a ≤ ((a ⇨ (⊥ : R.Omega)) ⇨ (⊥ : R.Omega)) :=
  Reentry.double_neg (R := R) a

-- Residuation helper: a ≤ b ⇒ c ↔ a ⊓ b ≤ c
example : a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  Reentry.le_himp_iff_inf_le (R := R) a b c

-- Nucleus convenience: image of implication with closed RHS is closed
-- R (x ⇨ R y) = x ⇨ R y (ambient α statement)
example (x y : α) : R (x ⇨ R y) = x ⇨ R y :=
  Reentry.map_himp_apply (R := R) x y

end LoF
end Tests
end HeytingLean
