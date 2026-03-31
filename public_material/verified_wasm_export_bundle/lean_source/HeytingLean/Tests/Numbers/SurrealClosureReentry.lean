import HeytingLean.Numbers.Surreal.ClosureReentry
import Mathlib.Order.Heyting.Basic

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal

/-!
Smoke test for the Surreal closure nucleus (Option A):
- Fixed points carry a Heyting algebra;
- Residuation/adjunction lemma is usable.
-/

section

open HeytingLean.Numbers.Surreal

def Rcl := surrealClosureReentry

#check (inferInstance : HeytingAlgebra ((Rcl).Omega))

variable (a b c : (Rcl).Omega)

-- Generic Heyting adjunction on Ω
example : a ⊓ b ≤ c ↔ a ≤ b ⇨ c := by
  -- use the HeytingAlgebra lemma
  exact (le_himp_iff (a := a) (b := b) (c := c)).symm

end

end Numbers
end Tests
end HeytingLean
