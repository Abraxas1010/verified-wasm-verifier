import HeytingLean.LoF.Combinators.Category.Groupoid

/-!
Compile-only sanity checks for the SKY “formal invertibility” layer.

This uses Mathlib's `Quiver.FreeGroupoid` on the one-step labeled rewrite quiver.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category
open CategoryTheory

#check (inferInstance : CategoryTheory.Groupoid MWFreeGroupoid)

-- Identity arrow in the free groupoid at a term.
example (t : Comb) : (GObj t ⟶ GObj t) := 𝟙 (GObj t)

-- Any multi-step path maps into the free groupoid.
example (t u : Comb) (p : LSteps t u) : (GObj t ⟶ GObj u) :=
  LSteps.toGroupoid p

end LoF
end Tests
end HeytingLean
