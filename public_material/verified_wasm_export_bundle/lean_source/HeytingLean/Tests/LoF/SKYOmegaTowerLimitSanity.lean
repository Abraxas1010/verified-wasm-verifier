import HeytingLean.LoF.Combinators.Category.OmegaTowerLimit

/-!
# Smoke test: ω-limit category for the strict SKY Arrow tower
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

#check CatTower
#check TowerLimit
#check TowerLimit.eval

#check MWLeftTower
#check MWRightTower

example : Category (TowerLimit MWLeftTower) := by
  infer_instance

end LoF
end Tests
end HeytingLean

