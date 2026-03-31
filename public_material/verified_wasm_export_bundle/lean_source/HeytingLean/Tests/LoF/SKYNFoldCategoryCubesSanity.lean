import HeytingLean.LoF.Combinators.Category.NFoldCategoryCubes

/-!
# Smoke test: strict cube layer for the Arrow tower (`Square MWQuotObj`)

This file checks that:
* `Square MWQuotObj` is a category (so cubes compose), and
* the equivalence `Square MWQuotObj ≌ MWCat 2` typechecks.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check MWCubeLayer
#check MWCube
#check squareEquiv_MWCat2'

private def X : MWQuotObj := ⟨Comb.K⟩

private def sq : Square MWQuotObj where
  f₁₂ := 𝟙 X
  f₁₃ := 𝟙 X
  f₂₄ := 𝟙 X
  f₃₄ := 𝟙 X
  fac := by simp

example : sq ⟶ sq := 𝟙 sq

example : (𝟙 sq) ≫ (𝟙 sq) = (𝟙 sq) := by simp

end LoF
end Tests
end HeytingLean

