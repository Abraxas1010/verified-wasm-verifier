import HeytingLean.Hyperseries.Category.NFoldCategoryArrow

namespace HeytingLean
namespace Tests
namespace Numbers

open CategoryTheory
open HeytingLean.Hyperseries.Category

#check HCat
#check (HCat 0)
#check (HCat 1)
#check (HCat 2)

example : Category (HCat 0) := by
  infer_instance

example : Category (HCat 2) := by
  infer_instance

example {X Y : HCat 0} (f : X ⟶ Y) :
    CategoryTheory.Arrow (HCat 0) := by
  exact CategoryTheory.Arrow.mk f

end Numbers
end Tests
end HeytingLean
