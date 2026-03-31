import HeytingLean.LoF.Combinators.Category.NFoldCategoryArsiwalla
import HeytingLean.LoF.Combinators.Category.NFoldCategoryArsiwallaLaws

/-!
# Smoke test: Arsiwalla-style structure maps for the strict `Arrow` tower

This file checks that:
- the generic `idArrow` / `compArrow` functors typecheck, and
- their specialization to the SKY strict tower (`MWIdArrow`, `MWCompArrow`) typechecks, and
- Mathlib’s `Square C ≌ Arrow (Arrow C)` equivalence can be instantiated at `MWQuotObj`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

#check idArrow
#check compArrow
#check Arsiwalla2Fold
#check Arsiwalla2Fold.ofCategory
#check MWIdArrow
#check MWCompArrow
#check MWArsiwalla2Fold
#check squareEquiv_MWCat2
#check idArrow_src
#check idArrow_tgt
#check compArrow_src
#check compArrow_tgt
#check unitLeft
#check unitRight
#check compArrow_unitLeft
#check compArrow_unitRight
#check compArrow_assoc_obj
#check compArrow_assoc

universe u v

example {C : Type u} [Category.{v} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (compArrow (C := C)).obj (ComposableArrows.mk₂ f g) = Arrow.mk (f ≫ g) := by
  rfl

example {C : Type u} [Category.{v} C] {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (compArrow (C := C)).obj (ComposableArrows.mk₂ (f ≫ g) h) =
      (compArrow (C := C)).obj (ComposableArrows.mk₂ f (g ≫ h)) := by
  simpa using compArrow_assoc_obj (C := C) f g h

end LoF
end Tests
end HeytingLean
